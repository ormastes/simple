# `test.system.qualified_pure_simple_runtime` cannot be resolved; its env probe was eaten by interpolation

- **Status:** closed (2026-11-15) for both defects; the specs still need an admitted self-hosted runtime
- **Where:** helper at `test/03_system/qualified_pure_simple_runtime.spl`.
  It is imported as `test.system.qualified_pure_simple_runtime` by 8 files:
  `profile_switchable_{container_algorithms,guard_acceptance,typed_plan_acceptance}_spec`,
  `profile_switchable_capture_arguments_it_spec`, `engine2d_font_offload_fallback_system_spec`,
  `streaming_parse_failure_receipt_spec`, `coverage_retained_parse_owner_spec`,
  `user_option_enum_match_lowering_system_spec`, and `test/fixtures/scv/db_causality_fixture`.

## Root cause
1. No resolver mapping exists from `test.system` to `test/03_system`, and no such
   mapping is designed: neither the seed nor the pure-Simple resolver has one.
   `test.system.*` resolves literally to `test/system/`, where shared system
   helpers live (`os_crypto_ref_helpers`, `browser_dom_identity_helpers`, ...).
   This helper was the one module placed under `test/03_system/`.
2. `"printf %s \"${SIMPLE_QUALIFIED_RUNTIME:-}\""` is an interpolating string.
   `{SIMPLE_QUALIFIED_RUNTIME:-}` was evaluated as a Simple expression, which gave
   `variable SIMPLE_QUALIFIED_RUNTIME not found`.

## Fix
- Moved the helper to `test/system/qualified_pure_simple_runtime.spl` (convention
  fix, no resolver change). Dropped the two now-stale `MODULE_MISSING` rows from
  `scripts/check/use_target_resolves_baseline.txt`.
- The shell probe now uses `$SIMPLE_QUALIFIED_RUNTIME` / `$SIMPLE_SEED_RUNTIME`
  (same sh semantics, no braces).

## Remaining (correct, fail closed)
`profile_switchable_container_algorithms_spec`: 11/11 now execute, then fail with
"no qualified pure-Simple runtime admitted". No self-hosted binary is deployed on
this macOS host, and the seed is correctly refused.
