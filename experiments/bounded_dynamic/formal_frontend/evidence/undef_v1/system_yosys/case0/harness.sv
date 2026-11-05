module M(input s,d);
      wire a,b; Ref reference(s,d,a); Cand candidate(s,d,b);
      always @* begin assume(!d); assert(a==b); end
    endmodule
