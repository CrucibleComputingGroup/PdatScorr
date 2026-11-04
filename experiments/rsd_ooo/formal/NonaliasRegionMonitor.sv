// Contract checker for the RSD LSQ candidate. Not part of the specialized core.
// Physical addresses are 22 bits: cacheability/IO flags plus 20 address bits.
// Check ALL execute events, including wrong-path and invalid-operand execution.
module NonaliasRegionMonitor #(
    parameter integer LOAD_LANES = 1,
    parameter integer STORE_LANES = 1
)(
    input logic clk,
    input logic rst,
    input logic [LOAD_LANES-1:0] execute_load,
    input logic [STORE_LANES-1:0] execute_store,
    input logic [21:0] load_phy_addr [LOAD_LANES],
    input logic [21:0] store_phy_addr [STORE_LANES]
);
    for (genvar l = 0; l < LOAD_LANES; l++) begin
        always @(posedge clk) begin
            if (!rst && execute_load[l]) begin
`ifdef PSCORR_FORMAL_ASSUME_REGION
                assume (load_phy_addr[l][21:16] == 6'b0);
`else
                assert (load_phy_addr[l][21:16] == 6'b0)
                    else $fatal(1, "Nonalias contract: load lane %0d addr=%h", l, load_phy_addr[l]);
`endif
            end
        end
    end
    for (genvar s = 0; s < STORE_LANES; s++) begin
        always @(posedge clk) begin
            if (!rst && execute_store[s]) begin
`ifdef PSCORR_FORMAL_ASSUME_REGION
                assume (store_phy_addr[s][21:16] != 6'b0);
`else
                assert (store_phy_addr[s][21:16] != 6'b0)
                    else $fatal(1, "Nonalias contract: store lane %0d addr=%h", s, store_phy_addr[s]);
`endif
            end
        end
    end
endmodule
