# Active generic-bound inference manual

Executable source: `test/01_unit/compiler/type_inference/generic_active_bound_inference_spec.spl`.
Requirement: REQ-GENERIC-ACTIVE-BOUNDS, prerequisite of the original full generic hardening plan.
Evidence status: all 18 scenarios authored, UNRUN. This manual is authored from the executable assertions; it is not runner-generated evidence.

Each fixture parses/lower real declarations, checks lowering success and required rows, and invokes public `infer_module`. Bounds/defaults attach to retained HIR binder identities because source transport remains a separate known gap. No fixture registers a solver trait or impl directly. Conditional fixtures require actual lowered generic impl binder rows and fail if absent.

| Scenario | Observable assertion |
|---|---|
| Explicit identity<i64>(1) | Actual call has one explicit type argument; zero HM errors |
| Explicit second binder positive | U=i64 accepted when T=bool lacks Marked |
| Explicit second binder negative | One TraitNotImplemented for Bool/Marked with a call span |
| Inferred positive | Value-inferred U=i64 accepted |
| Inferred negative | Value-inferred U=bool rejected |
| Var parity | Changing only resolved callee form preserves the bound failure |
| Conditional closure positive | Marked<T> requires and finds Other<i64> |
| Conditional closure negative | Missing Other<i64> becomes the concrete HM diagnostic |
| Ambiguity | Duplicate actual impl candidates produce the ambiguity HM error |
| Parameterized bound | Marked<i64> is refused, not erased |
| Explicit arity | Two written types for one binder produce the owning error |
| Generic forwarding | Exact caller bound discharges the symbolic obligation |
| Missing caller bound | Symbolic argument without evidence is rejected |
| Partial/default argument | Unused U defaults to i64 before its bound is solved |

Every inference fixture asserts the new pending-call queue is empty afterward. Driver warning/error policy, runtime, native memory/performance, whole-source parsing, methods, indirect calls and cross-module admission are not certified by this manual. Required execution and broader compatibility checks are owned by the root verification lane and remain UNRUN.

Revision 2 adds four actual module negatives. A missing trait row, a trait ID naming a Struct, a foreign-owned caller TypeParam, and a function ID naming a Struct each produce exactly one owning metadata error before any FunctionBoundContext or bound map is published. Existing valid generic forwarding remains the positive control. These scenarios are UNRUN. Broad Throws/Union/Isolated substitution behavior remains unqualified.
