# TargetHIR context identity

Executable specification: `test/01_unit/compiler/hir/target_hir_context_identity_spec.spl`.
Status: authored, unexecuted; runtime verification and manual generation were
omitted at the user's request. Source review does not qualify native execution.

The v2 target identity length-frames all 13 `MirTargetContext` fields in a fixed
order: architecture, OS, ABI, backend, version, build profile, subarchitecture,
CPU tier, collection policy, memory budget, optimization level, trace state and
collection target admission. Existing v1 target ids intentionally miss v2 keys;
there is no old-key fallback. Snapshot and region identity formats are unchanged.

| Scenario | Expected behavior |
|---|---|
| Debug and release | The same guard alternatives select different arms and have distinct identities. |
| Baseline and AVX-512 tier | SIMD class selection and target identity both differ. |
| Context field changes | Changing any one context field changes the identity; equal contexts stay equal. |
| Delimiter-bearing values | Embedded separators cannot move content across framed field boundaries. |
| Old-key invalidation | The default context uses the v2 namespace and cannot reuse the old target id. |
