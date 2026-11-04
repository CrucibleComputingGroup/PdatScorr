// Original RSD components, fixed MSHR2; scalar/packed observation boundary.
// No source cuts, new admission gates, output masks, or initialization changes.
import BasicTypes::*;
import CacheSystemTypes::*;
import MemoryTypes::*;
import ActiveListIndexTypes::*;

module MshrObserved (
    input logic clk, rst,
    input logic [MSHR_NUM-1:0] init_mshr, init_store, init_uncache, can_release,
    input PhyAddrPath [MSHR_NUM-1:0] init_addr,
    input ActiveListIndexPath [MSHR_NUM-1:0] init_alptr,
    input logic [MSHR_NUM-1:0] cache_grant,
    input DCachePortMultiplexerTagOut [MSHR_NUM-1:0] cache_tag_in,
    input DCachePortMultiplexerDataOut [MSHR_NUM-1:0] cache_data_in,
    input VectorPath stored_line,
    input logic [DCACHE_LINE_BYTE_NUM-1:0] stored_byte_we,
    input logic cache_flushing,
    input logic recovery_valid, recovery_all,
    input ActiveListIndexPath recovery_head, recovery_tail,
    input MemReadAccessReq ic_request,
    input logic write_busy,
    input MemWriteSerial next_write_serial,
    input MemAccessResponse write_response,
    input logic response_valid,
    input MemAccessSerial response_id,
    input MemoryEntryDataPath response_data,
    output logic [MSHR_NUM-1:0] cache_req, mshr_valid,
    output DCachePortMultiplexerIn [MSHR_NUM-1:0] cache_out,
    output PhyAddrPath [MSHR_NUM-1:0] mshr_addr,
    output MSHR_Phase [MSHR_NUM-1:0] mshr_phase,
    output DCacheLinePath [MSHR_NUM-1:0] mshr_data,
    output logic flush_complete,
    output PhyAddrPath memory_addr,
    output MemoryEntryDataPath memory_write_data,
    output logic read_accept, write_accept,
    output MemAccessSerial allocated_id,
    // The I-cache consumes ack/serial only (ICache.sv:425-428). The shared
    // acknowledgement type's wserial member is unassigned by the original
    // MemoryAccessController and is not a functional I-cache output.
    output logic [MEM_ACCESS_SERIAL_BIT_SIZE:0] ic_ack,
    output MemAccessResult ic_result
);
    DCacheIF dc(clk, rst, rst);
    CacheSystemIF bus(clk, rst);
    RecoveryManagerIF recovery(clk, rst);
    logic free_full, free_empty;

    DCacheMissHandler handler(dc, recovery);
    DCacheMemoryReqPortArbiter arbiter(dc);
    DCacheMemoryReqPortMultiplexer mux(dc);
    MemoryAccessController controller(
        .port(bus), .nextMemReadSerial(allocated_id),
        .nextMemWriteSerial(next_write_serial),
        .memReadData(response_data), .memReadDataReady(response_valid),
        .memReadSerial(response_id), .memAccessResponse(write_response),
        .memAccessReadBusy(free_empty),
        .memAccessWriteBusy(write_busy), .memAccessAddr(memory_addr),
        .memAccessWriteData(memory_write_data), .memAccessRE(read_accept),
        .memAccessWE(write_accept)
    );
    // Same original FreeList and return/pop handshake as Axi4Memory.sv:170-195.
    FreeList #(.SIZE(1 << MEM_ACCESS_SERIAL_BIT_SIZE),
               .ENTRY_WIDTH(MEM_ACCESS_SERIAL_BIT_SIZE)) ids (
        .clk(clk), .rst(rst), .push(response_valid),
        .pop(read_accept && !free_empty), .pushedData(response_id),
        .full(free_full), .empty(free_empty), .headData(allocated_id)
    );

    always_comb begin
        recovery.toRecoveryPhase = recovery_valid;
        recovery.flushAllInsns = recovery_all;
        recovery.flushRangeHeadPtr = recovery_head;
        recovery.flushRangeTailPtr = recovery_tail;
        dc.dcFlushing = cache_flushing;
        dc.storedLineData = stored_line;
        dc.storedLineByteWE = stored_byte_we;
        for (int i=0; i<MSHR_NUM; i++) begin
            dc.initMSHR[i] = init_mshr[i];
            dc.initMSHR_Addr[i] = init_addr[i];
            dc.initMSHR_ActiveListPtr[i] = init_alptr[i];
            dc.isAllocatedByStore[i] = init_store[i];
            dc.isUncachable[i] = init_uncache[i];
            dc.mshrCanBeInvalidDirect[i] = can_release[i];
            dc.mshrCacheGrt[i] = cache_grant[i];
            dc.mshrCacheMuxTagOut[i] = cache_tag_in[i];
            dc.mshrCacheMuxDataOut[i] = cache_data_in[i];
            cache_req[i] = dc.mshrCacheReq[i];
            cache_out[i] = dc.mshrCacheMuxIn[i];
            mshr_valid[i] = dc.mshrValid[i];
            mshr_addr[i] = dc.mshrAddr[i];
            mshr_phase[i] = dc.mshrPhase[i];
            mshr_data[i] = dc.mshrData[i];
        end
        flush_complete = dc.mshrFlushComplete;
        bus.icMemAccessReq = ic_request;
        bus.dcMemAccessReq.valid = dc.memValid;
        bus.dcMemAccessReq.we = dc.memWE;
        bus.dcMemAccessReq.addr = dc.memAddr;
        bus.dcMemAccessReq.data = dc.memData;
        dc.memReqAck = bus.dcMemAccessReqAck.ack;
        dc.memSerial = bus.dcMemAccessReqAck.serial;
        dc.memWSerial = bus.dcMemAccessReqAck.wserial;
        dc.memAccessResult = bus.dcMemAccessResult;
        dc.memAccessResponse = bus.dcMemAccessResponse;
        ic_ack = {bus.icMemAccessReqAck.ack, bus.icMemAccessReqAck.serial};
        ic_result = bus.icMemAccessResult;
    end
endmodule
