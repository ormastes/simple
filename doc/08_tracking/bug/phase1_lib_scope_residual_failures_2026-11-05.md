# Phase 1 (seed) lib-scope run: residual failures after the 2026-11-04/05 lanes

- **Filed:** 2026-11-05 (libbug coordinator)
- **Status:** open (tracking)
- **Run:** all 3933 `test/01_unit/lib/**/*_spec.spl` files, per file, on the seed, release `b9465b5cdb5`:
  3221 OK / 693 ERROR / 17 TIMEOUT; tests 36510 passed / 2186 failed.
  Goal areas failing files: sosix 0, nogc_async_mut 35, nogc_sync_mut 66, common 213.
- **Fixed since (PRs, all merged to release/1.0.0):** #6738, #6741, #6743, #6744 (lib + stale specs),
  #6746, #6748, #6749, #6753 (common), interpreter roots #6739, #6742, #6745, #6747, #6750, #6752.
- **Residual classes:** spec ahead of lib (missing modules/APIs, e.g. enterprise_*, hal_*,
  domain_arena_v2, debug *_v1, damage_tiles dirty API); host/env (Windows-only gaps, GPU, QEMU,
  Linux io_uring); interpreter roots with repros (e.g. `u8 * i64` narrows to u8); a few
  undiagnosed specs (zstd_sequence_fse_execution bit-level, process_observation_v4, jwt_rfc7519_kat).
- **Evidence (local, not in git):** per-file results and per-area triage were kept in the
  coordinator scratch (`p1suite/lib_results_final.tsv`, `triage_*.tsv`, `interp_repros_*.tsv`);
  re-run on the current seed to refresh before acting.

## Fix (2026-11-13) — jwt_rfc7519_kat (lane fA)

`jwt_rfc7519_kat_spec.spl` was 1/8 on the seed: every verify path raised
`variable 'idx3' not found` from `_b64u_decode` in `src/os/crypto/jwt.spl`, which
declared `idx3` as a branch-local `val` inside `if i + 2 < clean_len:` and then read
it in the sibling `if i + 3 < clean_len:` branch. Same defect and same fix as
`paseto.spl` (5294ff50d07): hoist `var idx3: i64 = 0` to the loop scope. Spec now
8/8 on the seed. Still residual in this umbrella: `process_observation_v4_spec.spl`
15/16 ("allows a pre-spawn rejection to retain absent process times"), and
`zstd_sequence_fse_execution` (not re-run).

## Fix (2026-11-13) — process_observation_v4 (lane n3)

"allows a pre-spawn rejection to retain absent process times" failed because
its fixture kept the golden packet's child ticket (words 6/7 = 3, 4). The
decoder (`observation_v4.spl`) rejects a Rejected receipt that keeps child
authority, and the runtime producer (`pov4_rejected` -> `pov4_words_base` memset,
`runtime_process_owned.c`) always writes a zero ticket. So the fixture was wrong
on every host, not only Windows. It now zeroes words 6/7: 16/16 on the seed.
Still residual: `zstd_sequence_fse_execution_spec.spl`, 6/15 on the seed
(2026-11-13). Its failures are TruncatedInput "zstd sequence bitstream bits"
and invalid offset/length/content-size, and all of them involve the predefined
OF/ML tables. Not diagnosed.
