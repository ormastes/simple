# HIR/native cache identity is invalidated by unrelated env changes

- **Date:** 2026-11-22
- **Status:** fixed (53a757bcfff) — re-verified green on release/1.0.0 tip 2026-11-25
- **Fixed:** 2026-11-24
- **Severity:** P2

## Symptom

A cosmetic environment change discards most of the HIR cache.

## Evidence

Phase 3 build f27 reused f26's cache dir but reported `[hir-cache] hits=206 misses=1707` (then hits=287 misses=1937). Between f26 and f27 the env gained `SIMPLE_ABI_ADMISSION_RECEIPT` and the cache root moved. Cache identity folds the whole `SIMPLE_*` environment, so about 90% of the HIR cache was lost.

## Repro

Run two consecutive builds over the same cache dir, adding one unrelated `SIMPLE_*` variable for the second; compare `[hir-cache]` hit counts.

## Workaround

Keep the `SIMPLE_*` environment byte-identical between builds that should share a cache.

## Fix direction

Key the cache on a declared allowlist of semantic env keys instead of the whole `SIMPLE_*` environment.

## Resolution (MP2)

1. **Module/native environment projection switched to explicit allowlist** (`src/compiler/80.driver/cache/native_build_environment_identity.spl`):
   - Preserved `NATIVE_BUILD_SEMANTIC_ENVIRONMENT_FIELDS_V1` (formal-pinned in `src/verification/cache_protocol/source_bindings.txt`) and complete capture validation in `native_build_environment_snapshot_fingerprint_v1`.
   - Replaced the ad-hoc denylist inside `native_build_module_environment_snapshot_fingerprint_v1` with `native_build_module_environment_field_allowed_v1`, allowing only semantic compiler/target/ABI fields from `NATIVE_BUILD_SEMANTIC_ENVIRONMENT_FIELDS_V1` (excluding cache-dir/root and shard-schedule fields in `NATIVE_BUILD_MODULE_EXCLUDED_FIELDS_V1`) plus `NATIVE_BUILD_MODULE_EXTRA_SEMANTIC_FIELDS_V1`, ignoring unrelated/cosmetic `SIMPLE_*`, harness, and cache-directory variables while keeping `SIMPLE_ABI_ADMISSION_RECEIPT` retained per `native_module_environment_projection_spec.spl`.
2. **HIR cache allowlist verified** (`src/compiler/80.driver/driver_hir_cache.spl`):
   - Confirmed `hir_cache_key` (`_hir_cache_env_switches`, `_hir_cache_key_target_part`), `hir_cache_header` (`_hir_cache_identity_scope`), and `hir_cache_dir` already key HIR cache entries on an explicit allowlist and ignore unrelated `SIMPLE_*` variables, cache directory variables, and `SIMPLE_ABI_ADMISSION_RECEIPT`.
3. **Cross-platform kernel running-image identity** (`src/compiler/80.driver/driver_build/incremental.spl`):
   - Added `_validated_kernel_image_path_v1` and `native_build_select_running_image_path_v1`, and updated `native_build_running_image_hash()` to resolve kernel-owned image paths on Windows (`windows_image_path()`) and macOS/Darwin (`darwin_image_path()`), using `/proc/self/exe` elsewhere without trusting `argv[0]` or `SIMPLE_BINARY`, eliminating Windows/macOS fallback to per-process `uncacheable-abi-admission-...-<pid>-<micros>` identities.
4. **Verification**:
   - `test/01_unit/compiler/driver/running_image_hash_kernel_owner_spec.spl` (5/5 passed)
   - `test/01_unit/compiler/driver/cache_identity_unrelated_env_invariance_spec.spl` (5/5 passed)
   - `test/01_unit/compiler/driver/native_module_environment_projection_spec.spl` (12/12 passed)
   - `test/01_unit/compiler/driver/native_cache_producer_identity_spec.spl` (15/15 passed)
   - `test/01_unit/compiler/cache/release_native_environment_identity_spec.spl` (4/4 passed)
   - `test/01_unit/compiler/driver/ctfe_env_inputs_identity_spec.spl` (3/3 passed)
   - `test/03_system/compiler/feature/native_zero_work_admission_spec.spl` (9/9 passed)
   - `test/01_unit/compiler/driver/kernel_image_digest_v1_spec.spl` (4/4 passed)
   - `test/01_unit/compiler/80.driver/compiler_exe_hash_candidates_spec.spl` (3/3 passed)
   - `test/01_unit/compiler/driver/native_module_cache_key_granularity_spec.spl` (11/11 passed)
   - `test/01_unit/compiler/driver/driver_cache_scope_publication_spec.spl` (8/8 passed)
   - `sh scripts/audit/direct-env-runtime-guard.shs --working`: `STATUS: PASS direct-env-runtime-guard`
5. **Re-verification on release/1.0.0 tip (2026-11-25, Rust seed)**:
   - `test/01_unit/compiler/driver/cache_identity_unrelated_env_invariance_spec.spl` (5/5 passed)
   - `test/01_unit/compiler/driver/native_module_environment_projection_spec.spl` (13/13 passed)
   - `test/01_unit/compiler/cache/release_native_environment_identity_spec.spl` (4/4 passed)
   - `test/01_unit/compiler/driver/running_image_hash_kernel_owner_spec.spl` (5/5 passed)
   - `test/01_unit/compiler/driver/native_cache_producer_identity_spec.spl` (15/15 passed)
   - `test/01_unit/compiler/driver/ctfe_env_inputs_identity_spec.spl` (3/3 passed)
   - `test/01_unit/compiler/driver/hir_cache_key_target_spec.spl` (4/4 passed)
   - `test/01_unit/compiler/driver/hir_cache_header_determinism_spec.spl` (4/4 passed)
   - `test/01_unit/compiler/lint/representation_boundary_autofix_spec.spl` (14/14 passed)

