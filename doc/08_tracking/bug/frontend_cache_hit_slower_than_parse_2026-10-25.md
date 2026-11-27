# Frontend parse-cache HIT slower than a cold parse (2026-10-25)

Status: fix in review (PR `work/frontend-cache-hit-spab-20261025` -> `release/1.0.0`).
Not yet re-measured on a stage2 rebuilt with the fix.

## Measured (frozen Windows stage2, 308 files)

| path | cost / file |
|------|-------------|
| cold parse | 130 ms |
| parse-cache HIT (`.fpc` text entry) | **455 ms** |

See row 5 of `stage3_hir_phase_cost_breakdown_2026-10-25.md`.

## Cause

The default hit path (`frontend.spl` -> `frontend_parse_cache_load`) read the
whole text entry, ran `sha256_text(blob)` -- which falls back to pure-Simple
SHA-256 (orders of magnitude slower) whenever `rt_tls13_sha256` does not return
32 bytes -- and then replayed the line blob through
`build_module_from_flat_pool_blob`. The packed `.spab` reader existed but was
opt-in (`SIMPLE_FRONTEND_SPAB=1`).

## Fix

1. `.spab` is the default store and hit format (`frontend_spab_enabled_v1`
   is on unless `SIMPLE_FRONTEND_SPAB=0`). A `.fpc` entry is written only on
   opt-out or when the packed store is refused. Cache keys/scopes unchanged.
2. Hit integrity is native-only: `sha256_u8_native_hex_or_empty` /
   `hash_algorithm_digest_native_v1`. Unavailable native digest => MISS
   (reason `native digest unavailable`), counted by
   `frontend_cache_native_digest_unavailable()` and printed as
   `native_digest_unavailable=` in the `[frontend-cache]` summary. The scope
   digest is memoised per process.
3. `SIMPLE_FRONTEND_CACHE_BOUNDARY_PROFILE=1` now prints
   `PARSECACHE load_ms= verify_ms= build_ms= format=spab|fpc`.

## What a hit still copies (honest)

- The file is mmapped on native (byte read in the interpreter).
- Section checksums and the body digest slice their input out of the map into
  a byte array before hashing (one copy of the body per hit).
- The flat pools are rebuilt from typed tokens read from the sections
  (`FlatPoolReader.from_tokens`) and the module is assembled from them; there
  is no line blob and no re-parse, but it is not a zero-rebuild "AST is the
  entry" hit yet (src_based_tldr_build_v1 rule 6 remains the target).

## Evidence

- `scripts/check/check-flat-ast-codec-complete.shs`: PASS, 150 pools.
- Spec `test/01_unit/compiler/frontend/frontend_cache_hit_path_spec.spl`:
  NOT run -- host blocker, `bin/simple test` fails with
  `parse: in src\lib\nogc_sync_mut\io\windows_redirected_process.spl:
  Unexpected token: expected Fn, found Colon`.

## Next

Re-run the 308-file stage2 with the profile flag and confirm hit < 130 ms.

## Follow-up 2026-11-05: supplied-source stores skipped by path-only capture dedup

After the `.spab` default landed, `test/01_unit/compiler/frontend/supplied_source_cache_key_spec.spl`
failed 3/7 under seed-interpreter `test` mode. Two distinct causes:

1. `frontend_parse_or_restore` (frontend.spl) consulted
   `flat_pool_capture_already_captured(file_path)` keyed by PATH ONLY. A
   supplied-source parse (same `file_path`, different source bytes, the very
   case commit 8e0f9d0eafd keyed the cache for) was treated as "already
   captured": the second and later contents under one path never captured,
   never stored, and never hit, so `frontend_parse_cache_load` returned ""
   and hits never incremented. Fixed by keying the dedup record by
   (path, cache content key) in `_FlatAstBridge/module_assembly.spl`
   (`flat_pool_capture_already_captured`/`flat_pool_capture_record`) and
   threading the caller's content key through `frontend.spl` and
   `80.driver/managed_parse_group.spl` (source_digest there).
2. The spec hand-crafts text `.fpc` entries and reads them through
   `frontend_parse_cache_load`, which only reads that format; with `.spab` the
   default store, a normal parse never writes `.fpc`. The spec now publishes
   `SIMPLE_FRONTEND_SPAB=0` alongside its private scope (the documented
   opt-out), selecting the line-cache format it tests.
