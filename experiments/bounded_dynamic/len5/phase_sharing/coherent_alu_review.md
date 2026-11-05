# Independent coherent-ALU abstraction review

The abstraction retains every execution of two identical, fully defined native
combinational ALU functions. At each cycle, equal complete input tuples select
one shared symbolic output; unequal tuples permit independent outputs. No
input-equality premise is assumed. The symbolic values may vary across cycles,
which adds behavior rather than imposing an unproved lifetime or data relation.
The original state and its clock/reset semantics remain in the proof model.

`signature` traces each result bit through supported combinational cells to the
named `ctl_i`, `rs1_i`, and `rs2_i` boundaries. Cell types, parameters, input
ports, bit positions, constants, and output positions enter the signature.
Undeclared external inputs, unsupported/stateful cells, cycles, multiple
drivers, and aliases between input roles are rejected. The two functions must
have identical signatures. A separate actual Yosys SAT check searches for any
undefined result on fully defined inputs; only an explicit UNSAT result permits
the replacement. Thus matching `x` defaults alone cannot authorize coherence.

Review found a missing interface-width guard: unused input bits can change a
role's width without changing the function signature. Concatenating tuples
with different role widths could compare an operand bit with a control bit and
incorrectly force shared results. The owner added exact per-role input-width
and result-width checks. The real interfaces are both control 4 + operand 64 +
operand 64, result 64, so this guard does not change their accepted shape. The
regression for differing unused control width now rejects before mutation.

Seven tests in `tests/unit/test_coherent_alu.py` pass. They use actual definedness
SAT and sequential SMT base/induction, not mocked statuses. A registered-output
identity proves; changing candidate control, first operand, or second operand
each gives a real counterexample because unequal tuples retain independent
symbolic outputs. Different native functions and observable undefined defaults
are rejected without mutating the input model. Structural checks verify the
full tuple, separate symbolic sources, original input ports, original sole reset
assumption, and retained native FF Q/clock/reset/parameters. The current 7 tests
plus the previous 14 native-state helper tests pass together: **21 passed in
4.06 seconds**. Source hashes and the command are in `coherent_alu_review.json`.

This is a proof-only overapproximation, not a hardware rewrite or evidence of
hardware savings. It cannot repair a missing observation or an invalid original
environment assumption. Failure on the abstraction can be conservative; a
timeout remains unknown. The generic tests do not establish equivalence of a
native LEN5 bank-sharing candidate whose final proof has not completed.
