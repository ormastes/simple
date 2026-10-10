# Native boxed text enum equality rejects equal contents

Status: OPEN — compiler/runtime prerequisite; no equality fix included here.

During release-source verification at `8303221132a0e44a739b30f92c3a1b7723534e86` plus the folded-global cache repair, the actual parser/HIR/MIR capsule creates two addresses and two immutable scalar statics. Comparing `MirTypeKind.Opaque("str")` or `MirConstValue.Str("trace")` to freshly constructed equal-content variants can still fail because generic native enum equality compares boxed handles. The runtime documents this limitation beside `rt_enum_new` in `src/runtime/runtime_native.c`: text payloads only intern when the same pointer is reused.

Evidence: `build/native_probe/traceability-release-sync-20261011-pass2/spec-run.log`; the focused regression now matches each required variant and asserts its concrete text/bool payload, while retaining all storage counts, symbol identity and scalar-type checks. This preserves the intended regression contract without relying on the independently broken equality operation.

Follow-up: route native enum equality through structural, type-aware comparison and add separately allocated equal-text payload regressions. The existing native SSpec zero-exit-on-failure defect remains separately recorded.
