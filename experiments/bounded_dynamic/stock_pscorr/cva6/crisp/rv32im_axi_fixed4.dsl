# RV32IM plus exact AXI timing: AR, AW and W are accepted at once; every read (last R
# beat) and every write (B) is answered exactly 4 cycles after acceptance.
version 2

include RV32I
include RV32M

grant_latency rd 0
grant_latency wr 0
grant_latency wdata 0
response_latency rd 4 4
response_latency wr 4 4
