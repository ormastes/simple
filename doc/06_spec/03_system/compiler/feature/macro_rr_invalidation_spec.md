# REQ-MACRO-RR Macro Reverse-Reference Invalidation

- Executable: `test/03_system/compiler/feature/macro_rr_invalidation_spec.spl`
- Requirements: `REQ-MACRO-RR-001`, `REQ-MACRO-RR-007`, `REQ-MACRO-RR-009`, `REQ-MACRO-RR-010` (test plan `doc/03_plan/sys_test/macro_rr_invalidation.md`)
- Evidence class: executable SPipe over the production BuildCache (`compiler.driver.driver_build.incremental`), the committed `.tldr` companions and the legacy `.rr` receipt.
- Status: hand-written manual, 2026-11-01. Regenerate with `bin/simple spipe-docgen test/03_system/compiler/feature/macro_rr_invalidation_spec.spl --output doc/06_spec --no-index` once a self-hosted `bin/release/<triple>/simple` exists; execution is UNRUN until then.

## Scenarios

- Publish a schema-2 receipt on `build_cache_persist` for a six-module fixture (provider with `twice`/`other`, nested `quad` that expands `twice!`, three sites, one unrelated module) recorded through a companion-bound BuildCache.
- Edit `twice`'s body only, detect changes with the tldr-aware cache: `Modified == [provider]`, `DependencyChanged == [nested, site_a, site_b]` exactly (not `site_c`, not `unrelated`), and `incremental_reverse_reference_fallback_reason_v1() == ""`.
- No-op run with no edit reports zero changes.
- Corrupt the `CURRENT` receipt pointer, edit the provider, detect: a non-empty fallback reason and every other entry `DependencyChanged` (whole-scope widening, fail closed).

## Pass criteria

Every scenario asserts with built-in matchers on real driver results; there is no `pass_todo` or tautological pass. The exact `DependencyChanged` set is the acceptance criterion for "no stale reuse and no over-invalidation": a body-only macro edit reaches its expansion sites and the dependent definer through the macro families of the receipt, while the unrelated module and the site of the untouched sibling macro stay reusable. The legacy V1 families are declared through their real owner seams in the fixture (as `reverse_reference_projection_receipt_spec` does) because the fixture does not compile.

Run: `bin/simple test test/03_system/compiler/feature/macro_rr_invalidation_spec.spl --mode=interpreter`.
