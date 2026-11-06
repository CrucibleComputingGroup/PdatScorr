# RV64IM plus the native platform's interface timing: every request is accepted at once;
# instruction responses arrive within 2 cycles (in order), load and store responses
# within 3 cycles of acceptance.
version 2

include RV32I
include RV32M
include RV64I
include RV64M

grant_latency instr 0
response_latency instr 2
grant_latency data_load 0
response_latency data_load 3
grant_latency data_store 0
response_latency data_store 3
