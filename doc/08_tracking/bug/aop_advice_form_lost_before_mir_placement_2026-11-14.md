# AOP advice form lost before MIR placement

- Severity: P1
- Status: verified for the scoped actual-MIR native projection
- Date: 2026-11-14

`weave_function` retained `MatchedAdvice.form` only until constructing
`AdviceCallInfo`. That record dropped the form, and `apply_weaving_result`
selected an injector solely from join-point kind. Execution after-success/error
therefore became a before hook. Function-context selectors also matched
instruction join points, producing duplicate or misplaced calls.

The fix preserves the required form field, limits context selectors to
Execution, and routes checked closed placements through the existing MIR
injectors. Instruction edits preserve original coordinates and advice order;
entry hooks use the actual declared entry block. Unsupported Around/proceed,
instruction error outcomes, malformed coordinates and missing entries fail
explicitly. PR #9177 independently ensures compiler diagnostics stop subsequent
execution/code generation.

Evidence: `/tmp/aspect-mir-placement-probe-20261114`. A receipt-matched
pure-Simple Stage 2 producer with core-c compiled and ran exact production
producer/selector/injector code and 191 actual transitive records, including
complete `MirFunction`. Exit zero verified form/kind propagation, entry/Ret/Abort
placement, instruction/tie order, four rejected requests and direct invalid
coordinate rejection. Source/binary hashes and the actual fixture are retained;
Astra independently checked them against the reviewed source. The initial
fixture's `Ret(nil)` was corrected to explicit `Ret(None)` before the passing
run; no production workaround was introduced.

This closes this form/placement bug at the native MIR transformation boundary.
It does not qualify whole-module import resolution, full CLI execution, complete
SSpec, true around advice, plugin loading or the overall feature plan.

Executable regression: `test/01_unit/compiler/mir/aop_static_placement_v1_spec.spl`.
Design: `doc/05_design/compiler/aspect_static_placement_v1_2026-11-14.md`.
