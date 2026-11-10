# Two perf specs blocked: no self-hosted Simple binary, and an unregistered font fixture (2026-08-18)

Status: BLOCKED 2026-11-11 (P3 lane ne19 triage, release/1.0.0 worktree) —
font-fixture blocker fixed in-tree; remaining blocker is deployment of a
pure-Simple self-hosted binary plus host-pinned baseline env, both outside a
P3 lane's grant.
Lane: lane-test-fix worktree, `bin/simple` -> shared Rust seed (rebuild forbidden in that lane)

## Addendum 2026-11-11 (lane ne19) — BLOCKED, one of two blockers resolved in-tree

Verified against the release/1.0.0 tree (worktree `bin/simple.exe` is still
the Rust seed v1.0.0-rc.1; no `bin/release/<triple>/` exists here).

**Blocker 2 (font fixture): FIXED in-tree.** `simple_2d_vector_fonts_perf_spec.spl`
now loads the fixture through the bytes API (`engine.load_font_bytes(PERF_FONT,
font_blob)`, line ~110) — exactly the remedy this doc specified — instead of
the registry-gated file-path API. The `SIMPLE_2D_BITMAP_BASELINE_NS` /
`SIMPLE_2D_BITMAP_BASELINE_CHECKSUM` pins remain env-supplied by design; this
lane did not invent values.

**Blocker 1 (self-hosted binary): unchanged.** `multicore_green_fanout_spec.spl`
still asserts `expect(stderr).to_equal("")` (lines ~215, ~225), which only a
deployed pure-Simple `bin/release/<triple>/simple` can satisfy; the seed's
mandatory banner makes every available binary fail that assertion. Per this
doc's own reasoning the assertion must not be relaxed.

**Grant addendum (verbatim unblock path):** in a lane authorized to run the
bootstrap build, deploy the self-hosted binary (`bin/simple build bootstrap`
or the release-channel equivalent) so `bin/release/<triple>/simple` exists,
then set `SIMPLE_2D_BITMAP_BASELINE_NS` / `SIMPLE_2D_BITMAP_BASELINE_CHECKSUM`
from the pinned host and run:

    bin/simple test test/05_perf/stress/multicore_green_fanout_spec.spl
    bin/simple test test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl

A P3 triage lane is not granted a bootstrap rebuild, so this row stays BLOCKED.

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
