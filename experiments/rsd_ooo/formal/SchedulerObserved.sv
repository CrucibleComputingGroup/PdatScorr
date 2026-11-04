// Scalar/packed synthesis boundary for unchanged RSD Scheduler + SelectLogic.
// All functional outputs are exported, including FP request/grant ports and
// pointers whose valid bits are false. No input assumptions or output masks.
// The generated no-FP candidate is justified only after an initial reset under
// the actual-write contract in SchedulerNoFPProof.sv, not for arbitrary state.
import BasicTypes::*;
import SchedulerTypes::*;
import MicroOpTypes::*;
module SchedulerObserved(
    input logic clk, rst, stall,
    input logic [DISPATCH_WIDTH-1:0] writes,
    input logic [DISPATCH_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM_BIT_WIDTH-1:0] write_ptr,
    input logic [DISPATCH_WIDTH-1:0][$bits(SchedulerEntry)-1:0] write_data,
    input logic [DISPATCH_WIDTH-1:0] memory_dependency,
    input IssueQueueOneHotPath ready, flush,
    input logic [MULDIV_ISSUE_WIDTH-1:0] div_free,
    input logic [FP_ISSUE_WIDTH-1:0] fp_div_free,
    output logic [ISSUE_WIDTH-1:0] selected, recovery_selected, wakeup_selected,
    output logic [ISSUE_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM_BIT_WIDTH-1:0] selected_ptr,
    output logic [ISSUE_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM_BIT_WIDTH-1:0] recovery_selected_ptr,
    output logic [ISSUE_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM_BIT_WIDTH-1:0] wakeup_selected_ptr,
    output logic [ISSUE_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM-1:0] selected_vector,
    output IssueQueueOneHotPath not_issued, recovery_not_issued,
    output IssueQueueOneHotPath int_requests, complex_requests, load_requests, store_requests, fp_requests,
    output logic [DISPATCH_WIDTH-1:0] dispatch_store, dispatch_load, wakeup_writes, wakeup_memory_dependency,
    output logic [DISPATCH_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM_BIT_WIDTH-1:0] wakeup_write_ptr,
    output logic [DISPATCH_WIDTH-1:0][$bits(SchedulerSrcTag)-1:0] source_tags,
    output logic [DISPATCH_WIDTH-1:0][$bits(SchedulerDstTag)-1:0] destination_tags,
    output logic wakeup_stall
);
    SchedulerIF port(clk, rst, 1'b0);
    WakeupSelectIF wakeup(clk, rst, 1'b0);
    RecoveryManagerIF recovery(clk, rst);
    MulDivUnitIF muldiv(clk, rst);
    FPDivSqrtUnitIF fpdiv(clk, rst);
    DebugIF debug(clk, rst);
    Scheduler scheduler(port, wakeup, recovery, muldiv, fpdiv, debug);
    SelectLogic selector(wakeup, recovery);
    always_comb begin
        port.stall = stall;
        wakeup.opReady = ready;
        recovery.flushIQ_Entry = flush;
        recovery.toRecoveryPhase = 1'b0; // Unread by the instantiated modules.
        for (int i=0; i<DISPATCH_WIDTH; i++) begin
            port.write[i] = writes[i];
            port.writePtr[i] = write_ptr[i];
            port.writeSchedulerData[i] = SchedulerEntry'(write_data[i]);
            port.memDependencyPred[i] = memory_dependency[i];
            dispatch_store[i] = wakeup.dispatchStore[i];
            dispatch_load[i] = wakeup.dispatchLoad[i];
            wakeup_writes[i] = wakeup.write[i];
            wakeup_write_ptr[i] = wakeup.writePtr[i];
            wakeup_memory_dependency[i] = wakeup.memDependencyPred[i];
            source_tags[i] = wakeup.writeSrcTag[i];
            destination_tags[i] = wakeup.writeDstTag[i];
        end
        for (int i=0; i<MULDIV_ISSUE_WIDTH; i++) muldiv.divFree[i] = div_free[i];
        for (int i=0; i<FP_ISSUE_WIDTH; i++) fpdiv.Free[i] = fp_div_free[i];
        for (int i=0; i<ISSUE_WIDTH; i++) begin
            selected[i] = port.selected[i];
            selected_ptr[i] = port.selectedPtr[i];
            recovery_selected[i] = recovery.selected[i];
            recovery_selected_ptr[i] = recovery.selectedPtr[i];
            wakeup_selected[i] = wakeup.selected[i];
            wakeup_selected_ptr[i] = wakeup.selectedPtr[i];
            selected_vector[i] = wakeup.selectedVector[i];
        end
        for (int i=0; i<ISSUE_QUEUE_ENTRY_NUM; i++) begin
            int_requests[i] = wakeup.intIssueReq[i];
            complex_requests[i] = wakeup.complexIssueReq[i];
            load_requests[i] = wakeup.loadIssueReq[i];
            store_requests[i] = wakeup.storeIssueReq[i];
            fp_requests[i] = wakeup.fpIssueReq[i];
        end
        not_issued = wakeup.notIssued;
        recovery_not_issued = recovery.notIssued;
        wakeup_stall = wakeup.stall;
    end
endmodule
