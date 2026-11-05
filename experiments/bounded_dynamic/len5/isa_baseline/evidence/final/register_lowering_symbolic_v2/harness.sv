module TemporalMiter(input [63:0] A,input [4:0] S);
      wire [2047:0] a,b;
      DemuxReference reference(.A(A),.S(S),.Y(a));
      DemuxCandidate candidate(.A(A),.S(S),.Y(b));
      always @* assert(a==b);
    endmodule
