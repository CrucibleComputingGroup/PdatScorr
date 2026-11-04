module original(input logic regStall, input logic [1:0] valid, taken, output logic [1:0] flushed);
  localparam FETCH_WIDTH=2; localparam FALSE=1'b0;
  typedef struct packed {logic valid;} Valid;
  typedef struct packed {logic predTaken;} Pred;
  Valid pipeReg[2]; Pred brPred[2]; logic isFlushed[2];
  always_comb begin
    for (int k=0;k<2;k++) begin
      pipeReg[k].valid=valid[k]; brPred[k].predTaken=taken[k]; flushed[k]=isFlushed[k];
    end
  end
  always_comb begin
        for (int i = 0; i < FETCH_WIDTH; i++) begin
            isFlushed[i] = FALSE;
            if (!regStall && pipeReg[i].valid && brPred[i].predTaken) begin
                for (int j = i + 1; j < FETCH_WIDTH; j++) begin
                    isFlushed[j] = pipeReg[j].valid;
                end

                break;
            end
        end

  end
endmodule
module canonical(input logic regStall, input logic [1:0] valid, taken, output logic [1:0] flushed);
  localparam FETCH_WIDTH=2; localparam FALSE=1'b0;
  typedef struct packed {logic valid;} Valid;
  typedef struct packed {logic predTaken;} Pred;
  Valid pipeReg[2]; Pred brPred[2]; logic isFlushed[2];
  always_comb begin
    for (int k=0;k<2;k++) begin
      pipeReg[k].valid=valid[k]; brPred[k].predTaken=taken[k]; flushed[k]=isFlushed[k];
    end
  end
  always_comb begin
        for (int i = 0; i < FETCH_WIDTH; i++) begin
            isFlushed[i] = FALSE;
        end
        for (int i = 0; i < FETCH_WIDTH; i++) begin
            if (!regStall && pipeReg[i].valid && brPred[i].predTaken) begin
                for (int j = i + 1; j < FETCH_WIDTH; j++) begin
                    isFlushed[j] = pipeReg[j].valid;
                end

                break;
            end
        end

  end
endmodule
module test;
 logic stall; logic[1:0] v,t; wire[1:0] a,b;
 original old(stall,v,t,a); canonical revised(stall,v,t,b);
 initial begin
   for(int i=0;i<32;i++) begin
     {stall,v,t}=5'(i); #1;
     if (a !== b) $fatal(1,"mismatch %d: %b != %b",i,a,b);
   end
   $display("PASS exhaustive 32 combinations original versus canonical fetch flush");
   $finish;
 end
endmodule
