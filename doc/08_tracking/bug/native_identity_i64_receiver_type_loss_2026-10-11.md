# Native identity integer receiver type loss

GitHub: https://github.com/ormastes/simple/issues/2983 (bug)

Status: explicit-type workaround prepared; native proof PENDING. Underlying compiler propagation repair remains separate.

C35 producer `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c` compiling the real identity fixture on source `0163d55daeae2e6e1cd65884c4d91299115d3281` emitted three unresolved `to_text` calls lowered to const-0 placeholders. Construction timed out after 300.746 seconds with 104 HIR modules passed and 64 MIR modules reported passed. No executable exists; placeholders independently disqualify native correctness and performance qualification.

Retained leaf HIR declares all four candidate receiver symbols as signed Int64: `fixed_size` (symbol 242), `lo_value` (352), `hi_value` (353), and `device_id` (336). Each receiver expression lacks type metadata and has unresolved method resolution. Integer `to_text` is a MIR builtin selected through `local_mir_type_of`, not a missing imported class method. The warnings omit spans, so their mapping to three specific candidates remains unproven. Do not replace this limitation with a claimed exact root cause.

The workaround adds explicit `i64` locals between those already-i64 bindings and their method calls. It adds no conversion, changes no values, and preserves the same optional branches, iteration order, serializer calls, and final canonical text. Both memory comparison variants must contain the identical workaround; only the scratch scope and fail-closed capsule guards may differ. Independent review and strict native construction followed by positive, negative, lifetime, and measured performance controls remain mandatory. The existing real fixture covers canonical digest, changed-input rejection, borrowed-input/digest survival after churn, and caller-owned scope behavior; it must run on a repaired native producer, not a seed or copied identity implementation.

Evidence root: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/source-authority-memory-20261011/c34-mir-identity-pair-attempt2`. See `assessment.json`, `to-text-candidate-hir-evidence.json`, and `before/compile/output.log`. The HIR cache, source/runtime receipts, and failed construction remain preserved.

The shared native fixture now also checks exact fixed-size/dynamic array identity text, bounded/unbounded dimension identity text, and ordered/reversed manifest device IDs through the actual production leaf helpers. These controls run before the timed repeated-digest section and are identical in both variants. They remain unexecuted until the consolidated next producer is available.
