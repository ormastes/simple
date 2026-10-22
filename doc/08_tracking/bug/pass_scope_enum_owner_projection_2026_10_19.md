# PassScope owner projection after descriptor unwrap

Status: source mitigation authored; compiler/spec execution UNRUN.
Requirement: REQ-ENUM-PASS-SCOPE, selected enum-hardening follow-up in
`doc/03_plan/sys_test/robust_any_enum_extension_2026-10-14.md`.

Historical audit groups 35, 36, and 38 diagnosed ambiguous bare `Module` /
`Function` variants on unresolved `found.scope` subjects in
`compiler.mir_opt.mod.run_named_pass_with_record` and
`run_pass_on_module_checked`. Their preceding optional descriptor unwrap lost
the record/enum subject evidence for the affected producer. This does not
establish a general repair to compiler type propagation.

The donor worktree `/home/yoon/dev/simple-utf8-external-text-root-20261018`
contains a bounded mitigation: explicitly type the unwrapped
`MirPassDescriptor`, project `found.scope` into a typed `PassScope`, and qualify
all three enum alternatives. This port applies only those two function-local
changes to the current owner. Status gates, structural before/after checks,
iteration ordering, unknown-request handling, and pass adapters are unchanged.
There is no fallback arm or synthesized scope. Future scope variants still
require an explicit dispatch decision.

Regression: `test/01_unit/compiler/mir_opt/pass_scope_enum_owner_spec.spl`
uses the real registry and checked dispatch with actual MIR functions/modules.
It verifies Module/Function/FsDriver descriptor ownership, the vectorization
alias, active Module rejection at the function-only boundary, real Module
dispatch with a no-op leaf, inactive scope skips, unknown-request outcomes,
and structural rejection before any status or unknown-request short circuit.

Current coverage limit: only AutoVectorize is Active, and it has Module scope.
Function passes are Skeleton/Disabled; FsDriver passes are AnalysisOnly.
Neither this regression nor the source mitigation claims execution of the
currently unreachable active Function/FsDriver scope branches, transformation
coverage, branch percentages, performance qualification, or general enum
exhaustiveness. Do not enable those passes merely to fill the coverage gap.

## Concrete adjacent test debt

`test/01_unit/compiler/mir_opt/pass_structural_verifier_spec.spl` still expects
pre-demotion active FsDriver behavior in these cases:

- `records an honest unchanged active function pass`: expects functions_seen
  1, Unchanged, and reason `no_change`; current `write_coalesce` is AnalysisOnly,
  so the retained contract is Skipped, functions_seen 0, and `analysis_only`.
- `records every write-coalesce candidate instead of a changed Boolean`:
  expects Transformed and two candidates from a now AnalysisOnly pass.
- `records every syscall-batch candidate instead of a changed Boolean`:
  likewise expects a transformation from now AnalysisOnly `syscall_batch`.

These stale expectations are identified by source inspection, not by a test
run. They are deliberately not rewritten by the PassScope port. Repair that
suite in its status-transition owner lane; do not weaken production status
gates. No full-suite PASS is claimed here.

Root owns qualified compiler/spec validation and independent exact-head
review. The author launched no compiler, native build, test runner, or doc
generator. Historical groups remain runtime-open until that evidence exists.
