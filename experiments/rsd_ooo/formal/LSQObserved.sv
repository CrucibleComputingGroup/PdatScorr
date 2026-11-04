// Actual RSD LQ+SQ synthesis harness. No assumptions, assertions, or debug ports.
// Forwarded data/miss are observed only when forwarding is selected; all
// queue status, allocation, conflict, and store commitment outputs are retained.
import BasicTypes::*;
import MemoryMapTypes::*;
import OpFormatTypes::*;
import LoadStoreUnitTypes::*;

module LSQObserved(
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
    input logic [1:0] load_map_type,
    output logic lq_allocatable, sq_allocatable,
    output logic [7:0] allocated_lq_ptrs, allocated_sq_ptrs,
    output logic [3:0] lq_head, sq_head,
    output logic sq_empty,
    output logic [4:0] sq_count,
    output logic [31:0] retired_data,
    output logic retired_cond_enabled, retired_word_we,
    output logic [3:0] retired_byte_we,
    output logic [19:0] retired_block_address,
    output logic conflict,
    output logic [18:0] conflict_pc,
    output logic forwarded,
    output logic [31:0] observed_forward_data,
    output logic observed_forward_miss
);
    LoadStoreUnitIF lsu(clk, rst, 1'b0);
    RecoveryManagerIF recovery(clk, rst);
    LoadQueue lq(lsu, recovery);
    StoreQueue sq(lsu, recovery);

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

        lq_allocatable = lsu.loadQueueAllocatable;
        sq_allocatable = lsu.storeQueueAllocatable;
        allocated_lq_ptrs = {lsu.allocatedLoadQueuePtr[1],lsu.allocatedLoadQueuePtr[0]};
        allocated_sq_ptrs = {lsu.allocatedStoreQueuePtr[1],lsu.allocatedStoreQueuePtr[0]};
        lq_head = recovery.loadQueueHeadPtr;
        sq_head = lsu.storeQueueHeadPtr;
        sq_empty = lsu.storeQueueEmpty;
        sq_count = lsu.storeQueueCount;
        retired_data = lsu.retiredStoreData;
        retired_cond_enabled = lsu.retiredStoreCondEnabled;
        retired_word_we = lsu.retiredStoreWordWE;
        retired_byte_we = lsu.retiredStoreByteWE;
        retired_block_address = lsu.retiredStoreLSQ_BlockAddr;
        conflict = lsu.conflict[0];
        conflict_pc = lsu.conflictLoadPC[0];
        forwarded = lsu.storeLoadForwarded[0];
        observed_forward_data = lsu.storeLoadForwarded[0] ? lsu.forwardedLoadData[0] : '0;
        observed_forward_miss = lsu.storeLoadForwarded[0] && lsu.forwardMiss[0];
    end
endmodule
