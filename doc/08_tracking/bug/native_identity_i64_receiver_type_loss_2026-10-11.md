# Native identity integer receiver type loss

GitHub: https://github.com/ormastes/simple/issues/2983 (bug)

Status: explicit-type workaround prepared; native proof PENDING. Underlying compiler propagation repair remains separate.

C35 producer `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c` compiling the real identity fixture on source `0163d55daeae2e6e1cd65884c4d91299115d3281` emitted three unresolved `to_text` calls lowered to const-0 placeholders. Construction timed out after 300.746 seconds with 104 HIR modules passed and 64 MIR modules reported passed. No executable exists; placeholders independently disqualify native correctness and performance qualification.

Retained leaf HIR declares all four candidate receiver symbols as signed Int64: `fixed_size` (symbol 242), `lo_value` (352), `hi_value` (353), and `device_id` (336). Each receiver expression lacks type metadata and has unresolved method resolution. Integer `to_text` is a MIR builtin selected through `local_mir_type_of`, not a missing imported class method. The warnings omit spans, so their mapping to three specific candidates remains unproven. Do not replace this limitation with a claimed exact root cause.

The workaround adds explicit `i64` locals between those already-i64 bindings and their method calls. It adds no conversion, changes no values, and preserves the same optional branches, iteration order, serializer calls, and final canonical text. Both memory comparison variants must contain the identical workaround; only the scratch scope and fail-closed capsule guards may differ. Independent review and strict native construction followed by positive, negative, lifetime, and measured performance controls remain mandatory. The existing real fixture covers canonical digest, changed-input rejection, borrowed-input/digest survival after churn, and caller-owned scope behavior; it must run on a repaired native producer, not a seed or copied identity implementation.

Evidence root: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/source-authority-memory-20261011/c34-mir-identity-pair-attempt2`. See `assessment.json`, `to-text-candidate-hir-evidence.json`, and `before/compile/output.log`. The HIR cache, source/runtime receipts, and failed construction remain preserved.

The shared native fixture now also checks exact fixed-size/dynamic array identity text, bounded/unbounded dimension identity text, and ordered/reversed manifest device IDs through the actual production leaf helpers. These controls run before the timed repeated-digest section and are identical in both variants. They remain unexecuted until the consolidated next producer is available.

## Code-read root cause and fix status (2026-11-03)

Status: fix-implemented-verification-pending.

- The `.to_text()` call on these receivers reaches the `MethodResolution.Unresolved`
  arm; the integer builtin is chosen at
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4939-4965`.
  Before `90d1f293648` (2026-10-20, after this bug's C35 evidence) the arm only
  accepted the receiver when `local_mir_type_of(local)` was a scalar. An
  `if val x = opt` binder's ExistsCheck slot keeps the Optional MIR shape
  (holding the raw word), so `local_mir_type_of` returned Optional and the call
  fell through to `reject_unresolved_method_call_v1` (line ~2256): the const-0
  placeholder and the warning.
- `90d1f293648` added a fallback: when the local is not a runtime-value local,
  `receiver_declared_type(receiver)`
  (`switch_operators_calls.spl:2813`, which reads the function-local HIR binding
  type, then the symbol type) yields `Int(64, signed)` (the C35 HIR shows exactly
  this for symbols 242/336/352/353). The arm then copies the word into an `i64`
  temp and renders it.
- Remaining limit: the fallback is skipped for `is_runtime_value_local` receivers.
- Regression spec: `test/01_unit/compiler/50.mir/i64_receiver_to_text_binding_spec.spl`
  uses the exact fixture shapes, without the typed aliases. It is not executed yet:
  on 2026-11-03 the deployed seed `bin/simple.exe run` fails before the spec runs
  with `parse: ... 70.backend/backend/_MirToLlvm/core_codegen.spl: Unterminated f-string`.
- Repro once a working binary exists: `bin/simple test test/01_unit/compiler/50.mir/i64_receiver_to_text_binding_spec.spl`
  (expect 0 diagnostics). Then rebuild the native identity fixture, confirm there
  are no `unresolved method call 'to_text'` warnings, and only then retire the
  `typed_*` aliases in `src/compiler/80.driver/native_capsule_mir_identity.spl:128,186,190,266`.
