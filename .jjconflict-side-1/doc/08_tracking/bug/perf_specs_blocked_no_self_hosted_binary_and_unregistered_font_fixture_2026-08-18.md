# Two perf specs blocked: no self-hosted Simple binary, and an unregistered font fixture (2026-08-18)

Status: OPEN
Lane: lane-test-fix worktree, `bin/simple` -> shared Rust seed (rebuild forbidden in this lane)

## 1. `test/05_perf/stress/multicore_green_fanout_spec.spl` — needs a self-hosted binary

Two real test defects were found and FIXED in this change:

- `unique_probe_path()` wrote the probe into `build/tmp/` without creating it.
  On a fresh worktree `rt_file_write_text` failed and `run_probe` returned the
  `98` (`probe_write_failed`) sentinel. Now `mkdir -p`s the directory.
- `simple_binary()` fell back to `src/compiler_rust/target/debug/simple`, which
  does not exist in a release/bootstrap worktree; the probe then exited `127`
  (command not found). Now falls back to `bin/simple`.

REMAINING BLOCKER (environment, not a test to weaken): the probes now build and
run and exit `0`, but the specs also assert `expect(stderr).to_equal("")`.
Every Simple binary available to this lane is the Rust bootstrap seed, and the
seed unconditionally prints its mandatory identity banner on stderr:

    WARNING: this Rust-built Simple binary is a bootstrap seed only; ...

plus a JIT-fallback `[INFO]`, a `[memory-guard]` line, and a `[gc-warning]`.
The empty-stderr assertion is correct and must NOT be relaxed: it is what makes
the row evidence-grade. The spec needs a deployed pure-Simple self-hosted
`bin/release/<triple>/simple` (`bin/simple build bootstrap`), which this lane is
explicitly forbidden to produce.

## 2. `test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl` — two blockers

Observed: every measured field is `0` and the run takes the early-return
sentinel branch, i.e. `engine.load_font(PERF_FONT)` returned `false`.

Root cause of the load failure (product/test contract mismatch, NOT fixed here):
`FontRenderer.try_load_runtime_ttf` first probes `browser_font_dylib_candidates()`
(`build/lib/libspl_fonts.so` and three siblings — none built in this lane), then
falls back to `FontRasterizer.load_selected(path)`
(`src/lib/nogc_sync_mut/sffi/spl_fonts.spl:198`), which returns `invalid()`
unless `selected_font_asset_candidate_for_path(path)` resolves — i.e. unless the
path is a REGISTERED selected-font asset. The spec writes an ad-hoc fixture to
`build/test-artifacts/05_perf/graphics_2d/simple_2d_vector_fonts/simple_ascii.ttf`,
which is not registered, so the file-path load API can never succeed for it.
The spec should either register the fixture asset or use
`Engine2D.load_font_bytes(path, blob)` (the bytes API validates the blob instead
of the registry).

Second, independent blocker (measurement environment): the spec's own docstring
requires the pinned host's retained baseline through
`SIMPLE_2D_BITMAP_BASELINE_NS` and `SIMPLE_2D_BITMAP_BASELINE_CHECKSUM`, and
asserts both are `> 0`. Neither variable is set anywhere in the repository —
they are host-pinned perf evidence. Supplying invented values would fabricate a
perf baseline, so this spec cannot go green on an unpinned, heavily loaded host
regardless of the load-font fix.
