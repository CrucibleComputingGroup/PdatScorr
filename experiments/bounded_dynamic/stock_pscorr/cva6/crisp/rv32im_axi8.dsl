# RV32IM plus AXI interface timing: AR, AW and W are accepted at once; every read
# (last R beat) and every write (B) is answered within 8 cycles of acceptance.
version 2

include RV32I
include RV32M

grant_latency rd 0
grant_latency wr 0
grant_latency wdata 0
response_latency rd 8
response_latency wr 8
