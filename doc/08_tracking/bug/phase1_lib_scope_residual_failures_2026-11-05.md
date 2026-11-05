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
