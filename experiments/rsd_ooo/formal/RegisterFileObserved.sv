// All functional RegisterFileIF ports, represented as scalar/packed top IO.
// Keeps every data-valid bit, FP/integer tag, write strobe and raw read result.
// No assumptions, address restrictions, input gating or output/reset masks.
// Compare matched guarded 64/48-entry source snapshots for area only; reducing
// capacity is not an equivalence transformation on unrestricted addresses.
import BasicTypes::*;
module RegisterFileObserved(
    input logic clk, rst, rstStart,
    input logic [INT_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] int_src_a, int_src_b,
    input logic [INT_ISSUE_WIDTH-1:0] int_we,
    input logic [INT_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] int_dst,
    input logic [INT_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] int_write_data,
    output logic [INT_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] int_read_a, int_read_b,
    input logic [COMPLEX_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] complex_src_a, complex_src_b,
    input logic [COMPLEX_ISSUE_WIDTH-1:0] complex_we,
    input logic [COMPLEX_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] complex_dst,
    input logic [COMPLEX_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] complex_write_data,
    output logic [COMPLEX_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] complex_read_a, complex_read_b,
    input logic [MEM_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] mem_src_a, mem_src_b,
    input logic [LOAD_ISSUE_WIDTH-1:0] mem_we,
    input logic [LOAD_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] mem_dst,
    input logic [LOAD_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] mem_write_data,
    output logic [MEM_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] mem_read_a, mem_read_b,
    input logic [FP_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] fp_src_a, fp_src_b, fp_src_c,
    input logic [FP_ISSUE_WIDTH-1:0] fp_we,
    input logic [FP_ISSUE_WIDTH-1:0][$bits(PRegNumPath)-1:0] fp_dst,
    input logic [FP_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] fp_write_data,
    output logic [FP_ISSUE_WIDTH-1:0][$bits(PRegDataPath)-1:0] fp_read_a, fp_read_b, fp_read_c
);
    RegisterFileIF port(clk, rst, rstStart);
    RegisterFile register_file(port);
    always_comb begin
        for (int i=0; i<INT_ISSUE_WIDTH; i++) begin
            port.intSrcRegNumA[i] = PRegNumPath'(int_src_a[i]);
            port.intSrcRegNumB[i] = PRegNumPath'(int_src_b[i]);
            port.intDstRegWE[i] = int_we[i];
            port.intDstRegNum[i] = PRegNumPath'(int_dst[i]);
            port.intDstRegData[i] = PRegDataPath'(int_write_data[i]);
            int_read_a[i] = port.intSrcRegDataA[i];
            int_read_b[i] = port.intSrcRegDataB[i];
        end
        for (int i=0; i<COMPLEX_ISSUE_WIDTH; i++) begin
            port.complexSrcRegNumA[i] = PRegNumPath'(complex_src_a[i]);
            port.complexSrcRegNumB[i] = PRegNumPath'(complex_src_b[i]);
            port.complexDstRegWE[i] = complex_we[i];
            port.complexDstRegNum[i] = PRegNumPath'(complex_dst[i]);
            port.complexDstRegData[i] = PRegDataPath'(complex_write_data[i]);
            complex_read_a[i] = port.complexSrcRegDataA[i];
            complex_read_b[i] = port.complexSrcRegDataB[i];
        end
        for (int i=0; i<MEM_ISSUE_WIDTH; i++) begin
            port.memSrcRegNumA[i] = PRegNumPath'(mem_src_a[i]);
            port.memSrcRegNumB[i] = PRegNumPath'(mem_src_b[i]);
            mem_read_a[i] = port.memSrcRegDataA[i];
            mem_read_b[i] = port.memSrcRegDataB[i];
        end
        for (int i=0; i<LOAD_ISSUE_WIDTH; i++) begin
            port.memDstRegWE[i] = mem_we[i];
            port.memDstRegNum[i] = PRegNumPath'(mem_dst[i]);
            port.memDstRegData[i] = PRegDataPath'(mem_write_data[i]);
        end
        for (int i=0; i<FP_ISSUE_WIDTH; i++) begin
            port.fpSrcRegNumA[i] = PRegNumPath'(fp_src_a[i]);
            port.fpSrcRegNumB[i] = PRegNumPath'(fp_src_b[i]);
            port.fpSrcRegNumC[i] = PRegNumPath'(fp_src_c[i]);
            port.fpDstRegWE[i] = fp_we[i];
            port.fpDstRegNum[i] = PRegNumPath'(fp_dst[i]);
            port.fpDstRegData[i] = PRegDataPath'(fp_write_data[i]);
            fp_read_a[i] = port.fpSrcRegDataA[i];
            fp_read_b[i] = port.fpSrcRegDataB[i];
            fp_read_c[i] = port.fpSrcRegDataC[i];
        end
    end
endmodule
