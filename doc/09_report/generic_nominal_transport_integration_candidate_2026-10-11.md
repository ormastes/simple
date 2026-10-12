# Generic nominal transport integration candidate

STATUS: UNQUALIFIED. Executable specifications and native fixtures are UNRUN.

This follow-up integrates the separately reviewed HIR nominal relocation helper
into monomorphization. A caller's concrete type arguments are relocated into the
template module before substitution. Both direct and method-call signatures are
relocated back into the caller before stamping the callee. Field-chain receiver
arguments first move from their declaration's table into the caller's table.
Final module assembly retains the relocated tables. Caller-side return inference
also receives the relocated return type, including enclosing generic calls.
Final assembly reserves the final specialization counter for every already-high
table, including callers that own no specialization themselves.

Missing or conflicting ownership records E-MONO-042 and leaves the original call
unresolved. Failed argument transport removes the provisional display-name cache
entry. Allocation reserves pending specialization ids whenever the destination
table already uses the high symbol range; compact tables remain compact. Type
parameter bounds count as symbol-bearing data for transport dispatch.

`test/01_unit/compiler/mono/generic_nominal_transport_spec.spl` prepares direct and
method rewrite assertions with an unrelated provider declaration at the same
numeric id, nested optional/array nominal arguments, provider-side substitution,
caller-side inference, allocation collision protection, failed-transport state,
and scalar fast-path behavior. These are source-reviewed candidate tests, not
runtime evidence. The parent lane owns MIR return-stamp consumption and the
third-owner native fixture; neither is established by this mono-only change.

Source checks passed: staged whitespace, direct-env-runtime guard (working and
staged), numbered-artifact guard, and zero executable specs under doc/06_spec.
Parent independent source review found and resolved the final counter gap;
the new full-pass regression also asserts returned provider import retention.

Required successor evidence: execute these specs with the rebuilt self-hosted
compiler, inspect native LLVM signatures and run exact-output native fixtures,
then run compiler/lib/MCP/LSP/core smoke gates. No seed test, source guard, Lean
model proof, or Hello result substitutes for that qualification.
