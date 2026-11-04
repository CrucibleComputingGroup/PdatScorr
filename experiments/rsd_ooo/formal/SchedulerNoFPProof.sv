// Actual original RSD scheduler + selector. No datapath is rewritten here.
import BasicTypes::*;
import SchedulerTypes::*;
import MicroOpTypes::*;
module SchedulerNoFPProof(
    input logic clk, rst, stall,
    input logic [DISPATCH_WIDTH-1:0] writes,
    input logic [DISPATCH_WIDTH-1:0][ISSUE_QUEUE_ENTRY_NUM_BIT_WIDTH-1:0] write_ptr,
    input logic [DISPATCH_WIDTH-1:0][$bits(SchedulerEntry)-1:0] write_data,
    input logic [DISPATCH_WIDTH-1:0] memory_dependency,
    input IssueQueueOneHotPath ready, flush,
    input logic [MULDIV_ISSUE_WIDTH-1:0] div_free,
    input logic [FP_ISSUE_WIDTH-1:0] fp_div_free
);
    SchedulerIF port(clk, rst, 1'b0);
    WakeupSelectIF wakeup(clk, rst, 1'b0);
    RecoveryManagerIF recovery(clk, rst);
    MulDivUnitIF muldiv(clk, rst);
    FPDivSqrtUnitIF fpdiv(clk, rst);
    DebugIF debug(clk, rst);
    Scheduler scheduler(port, wakeup, recovery, muldiv, fpdiv, debug);
    SelectLogic selector(wakeup, recovery);
    logic initial_cycle = 1'b1;
    always_ff @(posedge clk) initial_cycle <= 1'b0;
    always_comb begin
        port.stall = stall;
        wakeup.opReady = ready;
        recovery.flushIQ_Entry = flush;
        recovery.toRecoveryPhase = 1'b0; // Not read by Scheduler/SelectLogic.
        for (int i=0; i<DISPATCH_WIDTH; i++) begin
            port.write[i] = writes[i];
            port.writePtr[i] = write_ptr[i];
            port.writeSchedulerData[i] = SchedulerEntry'(write_data[i]);
            port.memDependencyPred[i] = memory_dependency[i];
`ifdef PSCORR_NO_FP_CONTRACT
            if (!rst && writes[i])
                assume(port.writeSchedulerData[i].opType != MOP_TYPE_FP);
`endif
        end
        for (int i=0; i<MULDIV_ISSUE_WIDTH; i++) muldiv.divFree[i] = div_free[i];
        for (int i=0; i<FP_ISSUE_WIDTH; i++) fpdiv.Free[i] = fp_div_free[i];
        if (initial_cycle) assume(rst);
        if (!rst) begin
            for (int i=0; i<ISSUE_QUEUE_ENTRY_NUM; i++) begin
                assert(!scheduler.notIssued[i] || !scheduler.isFP[i]);
                assert(!wakeup.fpIssueReq[i]);
            end
            for (int i=0; i<FP_ISSUE_WIDTH; i++) begin
                assert(!port.selected[INT_ISSUE_WIDTH+COMPLEX_ISSUE_WIDTH+MEM_ISSUE_WIDTH+i]);
                assert(!recovery.selected[INT_ISSUE_WIDTH+COMPLEX_ISSUE_WIDTH+MEM_ISSUE_WIDTH+i]);
            end
            assert(selector.fpGrant == 0);
            // Retain useful dynamic scheduling across all non-FP classes.
            cover((|(scheduler.notIssued & scheduler.isInt)) &&
                  (|(scheduler.notIssued & scheduler.isComplex)) &&
                  (|(scheduler.notIssued & scheduler.isLoad)) &&
                  (|(scheduler.notIssued & scheduler.isStore)));
        end
    end
endmodule
