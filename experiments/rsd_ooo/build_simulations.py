#!/usr/bin/env python3
"""Build isolated RSD variants with nonintrusive C++ resource/event tracing.

The original pinned RTL checkout is never modified. Capacity controls independently
vary LQ/SQ, ROB, IQ, or the coupled INT/FP physical-register counts. The optional
PRF reset guard is a separately identified compatibility RTL change. Monitoring
adds read-only C++ observers and simulation helpers, without driving processor state.
The generated-member names are pinned to RSD 7b65f6b and Verilator 4.228.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
REV = "7b65f6ba0bce58d4d859082660123b7100aae975"

DECL = r'''
    if (helper->PSCORR_ROB != PSCORR_ROB_CAPACITY || ISSUE_QUEUE_ENTRY_NUM != PSCORR_IQ_CAPACITY ||
        helper->PSCORR_LQ != PSCORR_LQ_CAPACITY || helper->PSCORR_SQ != PSCORR_SQ_CAPACITY ||
        helper->PSCORR_MSHR != 2 || helper->PSCORR_INT_PRF != PSCORR_PRF_CAPACITY || helper->PSCORR_FP_PRF != PSCORR_PRF_CAPACITY) {
        std::cerr << "Pscorr build configuration mismatch\n";
        return 2;
    }
    std::cout << "Pscorr config: rob=" << helper->PSCORR_ROB << ",iq=" << ISSUE_QUEUE_ENTRY_NUM
              << ",lq=" << helper->PSCORR_LQ << ",sq=" << helper->PSCORR_SQ
              << ",mshr=" << helper->PSCORR_MSHR << ",int_prf=" << helper->PSCORR_INT_PRF
              << ",fp_prf=" << helper->PSCORR_FP_PRF << '\n';
    // Pscorr experiment instrumentation: read-only, post-rising-edge samples.
    std::ofstream resourceCsv(TEST_CODE + "/resource.csv");
    std::ofstream memoryCsv(TEST_CODE + "/memory_events.csv");
    resourceCsv << "cycle,lq,sq,rob,iq,mshr,lq_not_allocatable,sq_not_allocatable,rename_stall,allocate_loads,allocate_stores,release_loads,release_stores,recovery\n";
    memoryCsv << "cycle,kind,address,reg_valid\n";
'''

SAMPLE = r'''
                // Counts are current registered occupancy. Allocation/release
                // signals are settled combinational events for the next edge.
                auto* ls = core->__PVT__loadStoreUnitIF;
                unsigned lq = core->__PVT__loadQueue__DOT__loadQueuePointer__DOT__regCount;
                unsigned sq = core->storeQueue->__PVT__storeQueuePointer__DOT__regCount;
                unsigned rob = core->activeList->__PVT__activeListPointer__DOT__regCount;
                unsigned iq = ISSUE_QUEUE_ENTRY_NUM - core->issueQueue->issueQueueFreeList->__PVT__count;
                unsigned mshr = 0, allocateLoads = 0, allocateStores = 0;
                for (auto value : ls->__PVT__mshrValid.m_storage) mshr += value != 0;
                for (auto value : ls->__PVT__allocateLoadQueue.m_storage) allocateLoads += value != 0;
                for (auto value : ls->__PVT__allocateStoreQueue.m_storage) allocateStores += value != 0;
                resourceCsv << cycle << ',' << lq << ',' << sq << ',' << rob << ',' << iq << ',' << mshr
                    << ',' << (lq > PSCORR_LQ_CAPACITY - RENAME_WIDTH - 1)
                    << ',' << (sq > PSCORR_SQ_CAPACITY - RENAME_WIDTH - 1)
                    << ',' << debugRegister.rnStagePipeCtrl.stall
                    << ',' << allocateLoads << ',' << allocateStores
                    << ',' << (ls->__PVT__releaseLoadQueue ? unsigned(ls->__PVT__releaseLoadQueueEntryNum) : 0)
                    << ',' << (ls->__PVT__releaseStoreQueueHead ? unsigned(ls->__PVT__releaseStoreQueueHeadEntryNum) : 0)
                    << ',' << debugRegister.toRecoveryPhase << '\n';
                for (unsigned lane = 0; lane < sizeof(ls->__PVT__executeLoad.m_storage)/sizeof(ls->__PVT__executeLoad[0]); ++lane) {
                    if (ls->__PVT__executeLoad[lane])
                        memoryCsv << cycle << ",load," << unsigned(ls->__PVT__executedLoadAddr[lane])
                                  << ',' << unsigned(ls->__PVT__executedLoadRegValid[lane]) << '\n';
                }
                for (unsigned lane = 0; lane < sizeof(ls->__PVT__executeStore.m_storage)/sizeof(ls->__PVT__executeStore[0]); ++lane) {
                    if (ls->__PVT__executeStore[lane])
                        memoryCsv << cycle << ",store," << unsigned(ls->__PVT__executedStoreAddr[lane])
                                  << ',' << unsigned(ls->__PVT__executedStoreRegValid[lane]) << '\n';
                }
'''

DEEP_DECL = r'''
    std::ofstream mshrCsv(TEST_CODE + "/mshr.csv");
    std::ofstream backingCsv(TEST_CODE + "/backing_memory.csv");
    std::ofstream predecodeCsv(TEST_CODE + "/predecode.csv");
    mshrCsv << "cycle,slot,valid,phase,address,init_request,init_address,init_by_store\n";
    backingCsv << "cycle,event,serial,address\n";
    predecodeCsv << "cycle,lane,pc,instruction,isa_allowed\n";
'''

DEEP_SAMPLE = r'''
                auto* dc = core->__PVT__dCache__DOT__port;
                for (unsigned slot = 0; slot < sizeof(dc->__PVT__mshrValid.m_storage)/sizeof(dc->__PVT__mshrValid[0]); ++slot) {
                    mshrCsv << cycle << ',' << slot << ',' << unsigned(dc->__PVT__mshrValid[slot])
                            << ',' << unsigned(dc->__PVT__mshrPhase[slot])
                            << ',' << unsigned(dc->__PVT__mshrAddr[slot])
                            << ',' << unsigned(dc->__PVT__initMSHR[slot])
                            << ',' << unsigned(dc->__PVT__initMSHR_Addr[slot])
                            << ',' << unsigned(dc->__PVT__isAllocatedByStore[slot]) << '\n';
                }
                auto* backing = top->Main_Zynq_Wrapper->main->memory;
                if (backing->pscorrReadRequest())
                    backingCsv << cycle << ",read_request," << unsigned(backing->pscorrReadRequestSerial())
                               << ',' << unsigned(backing->pscorrReadRequestAddress()) << '\n';
                if (backing->pscorrReadResponseValid())
                    backingCsv << cycle << ",read_response," << unsigned(backing->pscorrReadResponseSerial()) << ",0\n";
                for (unsigned lane = 0; lane < DECODE_WIDTH; ++lane) {
                    const auto& pd = core->__PVT__pdStage__DOT__pipeReg[lane];
                    if (helper->PreDecodeStageRegPath_valid(pd)) {
                        unsigned insn = helper->PreDecodeStageRegPath_insn(pd);
                        unsigned opcode = insn & 127;
                        bool allowed = opcode == 0x03 || opcode == 0x23 || opcode == 0x13 ||
                            opcode == 0x37 || opcode == 0x17 || opcode == 0x63 || opcode == 0x67 ||
                            opcode == 0x6f || opcode == 0x0f || opcode == 0x73 ||
                            (opcode == 0x33 && (insn >> 25) != 1);
                        predecodeCsv << cycle << ',' << lane << ',' << helper->PreDecodeStageRegPath_addr(pd)
                                     << ',' << insn << ',' << allowed << '\n';
                    }
                }
'''

HELPER = r'''
// Pscorr simulation-only typed accessors; no packed-layout assumptions.
`RSD_MAKE_STRUCT_ACCESSOR(PreDecodeStageRegPath, logic, valid)
`RSD_MAKE_STRUCT_ACCESSOR(PreDecodeStageRegPath, InsnPath, insn)
function automatic AddrPath PreDecodeStageRegPath_addr(PreDecodeStageRegPath e);
    /*verilator public*/
    return ToAddrFromPC(e.pc);
endfunction
'''

MEMORY_HELPER = r'''
`ifdef RSD_FUNCTIONAL_SIMULATION_VERILATOR
// Typed simulation-only accessors keep observed aliases live in Verilator.
function automatic logic pscorrReadRequest();
    /*verilator public*/
    return memReadAccessAck;
endfunction
function automatic MemAccessSerial pscorrReadRequestSerial();
    /*verilator public*/
    return nextNextMemReadSerial;
endfunction
function automatic AddrPath pscorrReadRequestAddress();
    /*verilator public*/
    return memAccessAddr;
endfunction
function automatic logic pscorrReadResponseValid();
    /*verilator public*/
    return memPipeReg[MEMORY_READ_PIPELINE_DEPTH-1].valid;
endfunction
function automatic MemAccessSerial pscorrReadResponseSerial();
    /*verilator public*/
    return memPipeReg[MEMORY_READ_PIPELINE_DEPTH-1].serial;
endfunction
`endif
'''

CONFIG_HELPER = r'''
// Simulation-only configuration exports for C++ manifest consistency checks.
localparam PSCORR_ROB /*verilator public*/ = ActiveListIndexTypes::ACTIVE_LIST_ENTRY_NUM;
localparam PSCORR_LQ /*verilator public*/ = LoadStoreUnitTypes::LOAD_QUEUE_ENTRY_NUM;
localparam PSCORR_SQ /*verilator public*/ = LoadStoreUnitTypes::STORE_QUEUE_ENTRY_NUM;
localparam PSCORR_MSHR /*verilator public*/ = MicroArchConf::CONF_DCACHE_MSHR_NUM;
localparam PSCORR_INT_PRF /*verilator public*/ = MicroArchConf::CONF_PSCALAR_NUM;
localparam PSCORR_FP_PRF /*verilator public*/ = MicroArchConf::CONF_PSCALAR_FP_NUM;
'''

FP_DECL = r'''
    std::ofstream fpCsv(TEST_CODE + "/fp_domain.csv");
    std::ofstream dispatchCsv(TEST_CODE + "/dispatch_events.csv");
    fpCsv << "cycle,scheduler_writes,fp_scheduler_writes,fp_issue_requests,fp_issue,fp_replay_entry,fp_record_entry,fp_pipe_valid\n";
    dispatchCsv << "cycle,lane,op_type\n";
'''

FP_SAMPLE = r'''
                auto* sched = core->__PVT__schedulerIF;
                auto* select = core->__PVT__wakeupSelectIF;
                unsigned writes=0, fpWrites=0, fpRequests=0, fpIssue=0, fpReplay=0, fpRecord=0, fpPipe=0;
                for (unsigned lane=0; lane<DISPATCH_WIDTH; ++lane) {
                    if (sched->__PVT__write[lane]) {
                        unsigned type = helper->SchedulerEntry_opType(sched->__PVT__writeSchedulerData[lane]);
                        ++writes;
                        fpWrites += type == helper->PSCORR_MOP_FP;
                        dispatchCsv << cycle << ',' << lane << ',' << type << '\n';
                    }
                }
                for (auto value : select->__PVT__fpIssueReq.m_storage) fpRequests += value != 0;
                for (unsigned lane=0; lane<FP_ISSUE_WIDTH; ++lane) {
                    fpIssue += sched->__PVT__fpIssue[lane] != 0;
                    fpReplay += sched->__PVT__fpReplayEntry[lane] != 0;
                    fpRecord += sched->__PVT__fpRecordEntry[lane] != 0;
                    fpPipe += helper->IssueStageRegPath_valid(core->__PVT__fpIsStage__DOT__pipeReg[lane]);
                }
                fpCsv << cycle << ',' << writes << ',' << fpWrites << ',' << fpRequests << ',' << fpIssue
                      << ',' << fpReplay << ',' << fpRecord << ',' << fpPipe << '\n';
'''

FP_HELPER = r'''
localparam PSCORR_MOP_FP /*verilator public*/ = MicroOpTypes::MOP_TYPE_FP;
`RSD_MAKE_STRUCT_ACCESSOR(SchedulerEntry, MicroOpType, opType)
`RSD_MAKE_STRUCT_ACCESSOR(IssueStageRegPath, logic, valid)
'''

RENAME_DECL = r'''
    std::ofstream renameCsv(TEST_CODE + "/rename_resources.csv");
    renameCsv << "cycle,int_free,fp_free,int_allocates,fp_allocates,int_releases,fp_releases,rename_recovery,rename_stall\n";
'''
RENAME_SAMPLE = r'''
                auto* rename = core->renameLogic;
                unsigned ia=0,fa=0,ir=0,fr=0;
                for (auto value : rename->__PVT__allocatePhyScalarReg.m_storage) ia += value != 0;
                for (auto value : rename->__PVT__allocatePhyScalarFPReg.m_storage) fa += value != 0;
                for (auto value : rename->__PVT__releasePhyScalarReg.m_storage) ir += value != 0;
                for (auto value : rename->__PVT__releasePhyScalarFPReg.m_storage) fr += value != 0;
                renameCsv << cycle << ',' << unsigned(rename->scalarFreeList->__PVT__count)
                          << ',' << unsigned(rename->scalarFPFreeList->__PVT__count)
                          << ',' << ia << ',' << fa << ',' << ir << ',' << fr
                          << ',' << unsigned(rename->__PVT__inRecoveryRMT)
                          << ',' << debugRegister.rnStagePipeCtrl.stall << '\n';
'''

def patch_once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--size", type=int, choices=[4,8,16], required=True)
    p.add_argument("--rob-size",type=int,choices=[16,32,64],default=64)
    p.add_argument("--issue-size",type=int,choices=[4,8,16,32,64],default=16)
    p.add_argument('--prf-size',type=int,choices=[32,48,64,128],default=64,
                   help='Coupled integer/FP physical-register count required by upstream equality assertion')
    p.add_argument('--prf-reset-guard',action='store_true',help='Explicit compatibility RTL change: guard out-of-range reset writes and clamp inactive RAM addresses; enables PRF48')
    p.add_argument('--rename-trace',action='store_true',help='Trace INT/FP free-register counts and allocate/release events')
    p.add_argument("--name")
    p.add_argument("--candidate", type=Path)
    p.add_argument('--fp-candidate',type=Path,help='Directory containing proven Scheduler.sv and/or IssueQueue.sv replacements')
    p.add_argument('--fp-domain-trace',action='store_true',help='Trace every actual scheduler write and FP issue/request/replay/record/pipe-valid event')
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--resume", action="store_true", help="Rebuild an existing snapshot, retaining prior logs")
    p.add_argument("--read-pipeline", type=int, default=5, choices=[5,10,20])
    p.add_argument("--deep-trace", action="store_true", help="Trace typed predecode ISA domain, MSHR slots, and backing read transactions")
    args = p.parse_args()
    if args.issue_size < 16:
        p.error('Pinned IQ has8 free-list write banks (6 issue+2 return ports): IQ4 violates the entries-multiple-of-banks assertion; IQ8 creates reversed one-entry-bank address slices and zero-width reset counter. Use16/32/64 without changing other RTL.')
    if args.prf_size==32 or (args.prf_size==48 and not args.prf_reset_guard):
        p.error('PRF32 leaves zero rename free-list entries; unmodified PRF48 reset writes48..63 outsideRAM. Use64/128 for pure-parameter controls, or explicitly --prf-reset-guard for separately labeled48 compatibility RTL.')
    if (args.rob_size,args.issue_size,args.prf_size)!=(64,16,64) and not args.name:
        p.error('--name is required for nondefault ROB/IQ/PRF capacities to keep builds isolated')
    if (args.candidate or args.fp_candidate) and (args.size,args.rob_size,args.issue_size,args.prf_size)!=(16,64,16,64):
        p.error('The retained candidate proofs cover only LQ/SQ16,ROB64,IQ16,PRF64. Other capacities need separate proof; do not transfer the pinned-instance result.')
    name = args.name or f"monitored_lq{args.size}_sq{args.size}"
    build = ROOT / "results" / name
    build.mkdir(exist_ok=args.resume)
    source = build / "source"
    source.mkdir(exist_ok=args.resume)
    original = ROOT / "rsd"
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=original, text=True).strip()
    assert commit == REV, commit
    for part in ("Src", "Tools"):
        if not (source / "Processor" / part).exists():
            shutil.copytree(original / "Processor" / part, source / "Processor" / part,
                            ignore=shutil.ignore_patterns("__pycache__", "*.log", "reg.out.hex", "serial.out.txt"))
    src = source / "Processor/Src"
    conf = src / "MicroArchConf.sv"
    config=(original / "Processor/Src/MicroArchConf.sv").read_text()
    overrides={'CONF_LOAD_QUEUE_ENTRY_NUM':(16,args.size),'CONF_STORE_QUEUE_ENTRY_NUM':(16,args.size),
               'CONF_ACTIVE_LIST_ENTRY_NUM':(64,args.rob_size),'CONF_ISSUE_QUEUE_ENTRY_NUM':(16,args.issue_size),
               'CONF_PSCALAR_NUM':(64,args.prf_size),'CONF_PSCALAR_FP_NUM':(64,args.prf_size)}
    for key,(old,new) in overrides.items():
        config=patch_once(config,f'{key} = {old};',f'{key} = {new};')
    fixed={'CONF_FETCH_WIDTH':2,'CONF_COMMIT_WIDTH':2,'CONF_REPLAY_QUEUE_ENTRY_NUM':20,'CONF_DCACHE_MSHR_NUM':2}
    for key,value in {**fixed,**{k:v[1] for k,v in overrides.items()}}.items():
        assert re.findall(r'localparam\s+'+key+r'\s*=\s*(\d+)\s*;',config)==[str(value)],(key,value)
    conf.write_text(config)
    regfile=src/'RegisterFile/RegisterFile.sv'
    register_text=(original/'Processor/Src/RegisterFile/RegisterFile.sv').read_text()
    if args.prf_reset_guard:
        for prefix,capacity,counter in (('reg', 'PSCALAR_NUM','regRstIndex'),('fpReg','PSCALAR_FP_NUM','fpRstIndex')):
            dest='dstRegNum' if prefix=='reg' else 'dstFPRegNum'
            old=f'{dest} [i] = {counter} + i;'
            assert register_text.count(old)==1,(old,register_text.count(old))
            guard=(old+f'\n                // Explicit non-power-of-two PRF reset compatibility.\n'
                   f'                if ({dest}[i] >= {capacity}) begin\n'
                   f'                    {prefix}WE[i] = FALSE;\n'
                   f"                    {dest}[i] = '0; // XOR/LVT reads even inactive write addresses.\n"
                   '                end')
            register_text=register_text.replace(old,guard)
    regfile.write_text(register_text)
    # Restore either requested candidate or pinned baseline on every invocation,
    # including resume; omitting --candidate must not leave an old cut in place.
    for module in ("LoadQueue.sv", "StoreQueue.sv"):
        origin = args.candidate / module if args.candidate else original / "Processor/Src/LoadStoreUnit" / module
        shutil.copy2(origin, src / "LoadStoreUnit" / module)
    fp_modules=[]
    for module in ('Scheduler.sv','IssueQueue.sv'):
        candidate=args.fp_candidate/module if args.fp_candidate else None
        origin=candidate if candidate and candidate.exists() else original/'Processor/Src/Scheduler'/module
        if candidate and candidate.exists():
            fp_modules.append(module)
        shutil.copy2(origin,src/'Scheduler'/module)
    if args.fp_candidate and not fp_modules:
        raise ValueError('--fp-candidate directory contains no recognized Scheduler.sv/IssueQueue.sv')
    memory_types = src / "Memory/MemoryTypes.sv"
    memory_types.write_text((original / "Processor/Src/Memory/MemoryTypes.sv").read_text().replace(
        "MEMORY_READ_PIPELINE_DEPTH = 5", f"MEMORY_READ_PIPELINE_DEPTH = {args.read_pipeline}"))
    cpp = src / "SysDeps/Verilator/TestMain.cpp"
    text = (original / "Processor/Src/SysDeps/Verilator/TestMain.cpp").read_text()
    text = patch_once(text, "    // Initialize dumpers\n", DECL + (DEEP_DECL if args.deep_trace else "") + (FP_DECL if args.fp_domain_trace else '') + (RENAME_DECL if args.rename_trace else '') + "\n    // Initialize dumpers\n")
    text = patch_once(text, "                GetDebugRegister(&debugRegister, top);", "                GetDebugRegister(&debugRegister, top);\n" + SAMPLE + (DEEP_SAMPLE if args.deep_trace else "") + (FP_SAMPLE if args.fp_domain_trace else '') + (RENAME_SAMPLE if args.rename_trace else ''))
    # The host CData type does not retain the narrower SV pointer wrap width.
    # Correct only the final architectural-register observation on ROB wrap.
    text = patch_once(text,'        alHeadPtr++;','        alHeadPtr = (alHeadPtr + 1) % PSCORR_ROB_CAPACITY;')
    text = f"#define PSCORR_LQ_CAPACITY {args.size}\n#define PSCORR_SQ_CAPACITY {args.size}\n#define PSCORR_ROB_CAPACITY {args.rob_size}\n#define PSCORR_IQ_CAPACITY {args.issue_size}\n#define PSCORR_PRF_CAPACITY {args.prf_size}\n" + text
    cpp.write_text(text)
    helper_file = src / "SysDeps/Verilator/VerilatorHelper.sv"
    helper_text = (original / "Processor/Src/SysDeps/Verilator/VerilatorHelper.sv").read_text()
    helper_text = patch_once(helper_text, "\nendpackage", "\n" + CONFIG_HELPER + (HELPER if args.deep_trace else '') + (FP_HELPER if args.fp_domain_trace else '') + "\nendpackage")
    helper_file.write_text(helper_text)
    memory_file = src / "Memory/Memory.sv"
    memory_text = (original / "Processor/Src/Memory/Memory.sv").read_text()
    if args.deep_trace:
        memory_text = patch_once(memory_text, " endmodule", "\n" + MEMORY_HELPER + "\n endmodule")
    memory_file.write_text(memory_text)
    verilator = ROOT / "tools/verilator-4.228"
    env = os.environ.copy()
    env["PATH"] = "/usr/bin:/bin:/usr/local/bin"
    env.pop("VERILATOR_BIN", None)
    env["RSD_VERILATOR_BIN"] = str(verilator / "bin/verilator")
    env["VERILATOR_ROOT"] = str(verilator)
    command = ["make", f"-j{args.jobs}", "-f", "Makefile.verilator.mk", f"VERILATOR_ROOT={verilator}"]
    manifest = {"core_commit": commit, "lq": args.size, "sq": args.size,
                'rob':args.rob_size,'iq':args.issue_size,'mshr':2,'integer_physical_registers':args.prf_size,
                'fp_physical_registers':args.prf_size,'replay_queue_entries':20,'fetch_rename_commit_width':2,
                'config_overrides':{k:{'original':v[0],'requested':v[1]} for k,v in overrides.items()},
                'observer_note':'C++ final-register observation explicitly wraps ROB pointer; no processor-state writes. Runtime checks actual elaborated capacities against requested manifest.',
                "memory_read_pipeline_depth": args.read_pipeline,
                "memory_service_note": "Only backing read-response pipeline stages varied; read/write busy-count parameters=2 (minimum accepted-request gap3 cycles), jitter modulo10, xorshift seed1987534242 unchanged. Total memory latency is not equal to pipeline depth.",
                "deep_trace": args.deep_trace,
                'fp_domain_trace':args.fp_domain_trace,
                'rename_trace':args.rename_trace,'prf_reset_guard':args.prf_reset_guard,
                'prf_reset_guard_scope':('INT/FP RegisterFile resetloops only: disable out-of-range writes and clamp inactive addresses to0. Counters/protocol unchanged; guard unreachable at64/128 power-of-two capacities.' if args.prf_reset_guard else None),
                'fp_candidate':str(args.fp_candidate.resolve()) if args.fp_candidate else None,
                'fp_candidate_modules':fp_modules,
                'candidate_proof_configuration_scope':({'lq':16,'sq':16,'rob':64,'iq':16,'integer_prf':64,'fp_prf':64,
                    'note':'Pinned-instance proof only; runtime workload-contract observation is separate.'} if args.candidate or args.fp_candidate else None),
                "candidate": str(args.candidate.resolve()) if args.candidate else None,
                "command": command, "cwd": str(src),
                "verilator_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=verilator, text=True).strip(),
                "monitor_sampling": "post-rising-edge occupancy; settled execution/event signals for next edge",
                "source_sha256": {str(f.relative_to(src)): hashlib.sha256(f.read_bytes()).hexdigest()
                                  for f in src.rglob("*") if f.is_file() and f.suffix in (".sv", ".cpp", ".h", ".mk")}}
    (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    start = time.monotonic()
    if (build / "build.log").exists():
        (build / "build.log").rename(build / f"build_previous_{time.time_ns()}.log")
    with (build / "build.log").open("w") as log:
        run = subprocess.run(command, cwd=src, env=env, stdout=log, stderr=subprocess.STDOUT)
    manifest["build_exit_code"] = run.returncode
    manifest["build_seconds"] = time.monotonic() - start
    if run.returncode == 0:
        binary = build / "VMain_Zynq_Wrapper"
        shutil.copy2(source / "Processor/Project/Verilator/obj_dir/VMain_Zynq_Wrapper", binary)
        manifest["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
    (build / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"{name}: exit={run.returncode}, seconds={manifest['build_seconds']:.1f}")
    return run.returncode

if __name__ == "__main__":
    raise SystemExit(main())
