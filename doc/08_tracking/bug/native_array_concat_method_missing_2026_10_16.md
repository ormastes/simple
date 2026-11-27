
## 2026-11-04 triage (n88b, opus-n88b): fix already landed, verification-pending

Fixed by `8bf5daec825` "preserve fresh array concat dispatch and element authority"
(`50.mir/_MirLoweringExpr/method_calls_literals.spl`, `method == "concat"` arm lowering to fresh
`rt_array_concat`), see `mir_array_concat_dispatch_missing_2026_10_16.md`. Seed run:
`test/01_unit/compiler/mir/array_concat_spec.spl` 1/1 pass. The `package_archive_cache.spl:417`
workaround (`+`) may be retired once stage3 passes
`test/01_unit/compiler/mir/array_concat_engine_native.spl` (expect `PASS array-concat-engine`).
