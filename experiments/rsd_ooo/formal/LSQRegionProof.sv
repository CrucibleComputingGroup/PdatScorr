// Actual RSD queue-state proof harness. Source modules are not rewritten.
import BasicTypes::*;
import MemoryMapTypes::*;
import OpFormatTypes::*;
import LoadStoreUnitTypes::*;

module LSQRegionProof(
    input logic clk, rst,
    input logic [1:0] allocate_load, allocate_store,
    input logic execute_load, execute_store,
    input logic load_reg_valid, store_reg_valid, store_cond_enabled,
    input logic [21:0] load_address, store_address,
    input logic [3:0] load_entry, store_entry,
    input logic [3:0] load_store_age_ptr, store_load_age_ptr,
    input logic [18:0] load_pc,
    input logic [$bits(MemAccessMode)-1:0] load_mode, store_mode,
    input logic [31:0] store_data,
    input logic release_load, release_store,
    input logic [1:0] release_load_count, release_store_count,
    input logic recovering,
    input logic [3:0] load_recovery_tail, store_recovery_tail,
    input logic [3:0] retired_store_ptr,
    input logic [1:0] load_map_type
);
    LoadStoreUnitIF lsu(clk, rst, 1'b0);
    RecoveryManagerIF recovery(clk, rst);
    LoadQueue lq(lsu, recovery);
    StoreQueue sq(lsu, recovery);
    logic initial_cycle = 1'b1;
    always_ff @(posedge clk) initial_cycle <= 1'b0;

    always_comb begin
        for (int i=0; i<2; i++) begin
            lsu.allocateLoadQueue[i] = allocate_load[i];
            lsu.allocateStoreQueue[i] = allocate_store[i];
        end
        lsu.executeLoad[0] = execute_load;
        lsu.executeStore[0] = execute_store;
        lsu.executedLoadAddr[0] = PhyAddrPath'(load_address);
        lsu.executedStoreAddr[0] = PhyAddrPath'(store_address);
        lsu.executedLoadRegValid[0] = load_reg_valid;
        lsu.executedStoreRegValid[0] = store_reg_valid;
        lsu.executedStoreCondEnabled[0] = store_cond_enabled;
        lsu.executedLoadQueuePtrByLoad[0] = load_entry;
        lsu.executedStoreQueuePtrByStore[0] = store_entry;
        lsu.executedStoreQueuePtrByLoad[0] = load_store_age_ptr;
        lsu.executedLoadQueuePtrByStore[0] = store_load_age_ptr;
        lsu.executedLoadPC[0] = load_pc;
        lsu.executedLoadMemAccessMode[0] = MemAccessMode'(load_mode);
        lsu.executedStoreMemAccessMode[0] = MemAccessMode'(store_mode);
        lsu.executedLoadMemMapType[0] = MemoryMapType'(load_map_type);
        lsu.executedStoreData[0] = store_data;
        lsu.executedStoreVectorData[0] = '0;
        lsu.releaseLoadQueue = release_load;
        lsu.releaseLoadQueueEntryNum = release_load_count;
        lsu.releaseStoreQueueHead = release_store;
        lsu.releaseStoreQueueHeadEntryNum = release_store_count;
        lsu.retiredStoreQueuePtr = retired_store_ptr;
        recovery.toRecoveryPhase = recovering;
        recovery.loadQueueRecoveryTailPtr = load_recovery_tail;
        recovery.storeQueueRecoveryTailPtr = store_recovery_tail;

        if (initial_cycle) assume(rst);
        if (!rst) begin
            assume(!execute_load || load_address[21:16] == 0);
            assume(!execute_store || store_address[21:16] != 0);
            for (int i=0; i<LOAD_QUEUE_ENTRY_NUM; i++) begin
                assert(!lq.loadQueue[i].finished || lq.loadQueue[i].address[19:14] == 0);
            end
            for (int i=0; i<STORE_QUEUE_ENTRY_NUM; i++) begin
                assert(!sq.storeQueue[i].finished || sq.storeQueue[i].address[19:14] != 0);
            end
            assert(!execute_store || lq.addrMatch[0] == 0);
            assert(!execute_load || sq.addrMatch[0] == 0);
            assert(!lsu.storeLoadForwarded[0]);
            assert(!execute_store || !lsu.conflict[0]);
            cover(execute_load && execute_store &&
                  lq.curCount > 0 && sq.curCount > 0 &&
                  lq.loadQueue[0].finished && sq.storeQueue[0].finished);
        end
    end
endmodule
