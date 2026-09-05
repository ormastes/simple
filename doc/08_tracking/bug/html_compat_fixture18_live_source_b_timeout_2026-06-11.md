# HTML Compat Fixture 18 Live Source-B Timeout

- **Status:** closed — all AC verified 2026-06-12
- **Date:** 2026-06-11
- **Lane:** Simple Web / Chromium HTML pixel parity

## Summary

`18_flex_grow_weights` is present in the HTML compat catalog and has checked-in
Chrome/Simple PPM baselines plus an exact `report.sdn`, but a fresh live run of
the source-B Simple renderer path currently times out before producing the
Simple PPM.

Follow-up diagnosis on 2026-06-11 narrowed the timeout to child runtime
selection in isolated worktrees, not to the fixture layout algorithm itself:

- Direct worker execution rendered and wrote the fixture in about `0.65s`.
- The parent harness passed in about `2.3s` when `SIMPLE_BINARY` was set to the
  active Simple compiler path.
- The parent harness timed out when it had to fall through automatic binary
  discovery. In clean worktrees, tracked wrappers such as `bin/release/simple`
  may exist without their architecture-specific native payload, and `_` is only
  `/usr/bin/env`, not the parent Simple binary.

Follow-up fix on 2026-06-11 made child runtime selection fail fast instead of
falling through to a stale or missing runtime:

- `html_compat_part1.spl` and `site_corpus_compat.spl` now accept only
  configured/local Simple child candidates that pass a bounded `--version`
  probe.
- With `SIMPLE_BINARY` set to the active runtime,
  `18_flex_grow_weights` still reports `RESULT: EXACT match` in about `2.7s`.
- In an isolated worktree with no runnable local Simple payload, the same
  command exits quickly with `no runnable Simple binary found for source B
  child; set SIMPLE_BINARY to the active runtime` instead of timing out.
- This does not change the renderer output and does not use blur, tolerance, or
  copied Chromium pixels.

## Reproduction

```sh
SIMPLE_LIB=src bin/simple run src/app/wm_compare/html_compat.spl --only=18_flex_grow_weights
```

Observed result on Linux:

```text
[html_compat] Chromium golden <-> Simple — 23 fixtures, 320x240
[html_compat] Fixture: 18_flex_grow_weights
[html_compat]   loading source A (checked-in Chromium golden)...
[html_compat]     ok  pixels=76800
[html_compat]   capturing source B (Simple browser engine)...
[html_compat]     fail: no runnable Simple binary found for source B child; set SIMPLE_BINARY to the active runtime
[html_compat]   RESULT: simple capture failed
```

The command exits with code `2`.

Known passing workaround:

```sh
SIMPLE_LIB=src SIMPLE_BINARY=/path/to/active/simple \
  bin/simple run src/app/wm_compare/html_compat.spl --only=18_flex_grow_weights
```

Observed result with the active local compiler:

```text
[html_compat] Fixture: 18_flex_grow_weights
[html_compat]     ok  pixels=76800
[html_compat]   RESULT: EXACT match
[html_compat] All fixtures accepted. Phase 2 progression complete.
```

## Notes

Do not fix this by adding a compact marker that bypasses the pure Simple render
path or by copying Chromium pixels into the Simple side. A valid fix must still
execute the Simple layout/raster path for the fixture, then serialize or compare
the resulting pixels within the harness timeout.

Likely areas to inspect:

- `src/app/wm_compare/simple_html_capture_worker.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- `src/app/wm_compare/html_compat_part1.spl`
- `bin/simple-interp`
- `bin/release/simple`

## Acceptance Criteria

- With `SIMPLE_BINARY` set to the active runtime, the reproduction command exits
  `0` without increasing blur/tolerance.
- Without a runnable local child runtime, the reproduction command fails quickly
  with a clear missing-runtime message instead of using `simple` from PATH or
  waiting for the render timeout.
- `test/09_baselines/html_compat/18_flex_grow_weights/report.sdn` records
  `simple: (capture success: true ...)`.
- The compare row remains exact: `exact: true`, `different_pixels: 0`,
  `match_pct_10000: 10000`.
- The fix must not rely on a machine-specific absolute compiler path; automatic
  child runtime discovery must either find a runnable local runtime or fail
  quickly with a clear missing-runtime error.

## Verification (2026-06-12)

Reproduced and verified on Linux (x86_64). No code changes needed — the fix
documented in Summary was already committed.

**Repro without SIMPLE_BINARY (automatic discovery via `bin/simple` symlink):**
```text
SIMPLE_LIB=src bin/simple run src/app/wm_compare/html_compat.spl --only=18_flex_grow_weights
[html_compat] Fixture: 18_flex_grow_weights
[html_compat]   loading source A...  ok  pixels=76800
[html_compat]   capturing source B...  ok  pixels=76800
[html_compat]   RESULT: EXACT match
elapsed ≈ 7s, exit 0
```

**report.sdn confirms all AC:**
```
simple: (capture success: true width: 320 height: 240 pixel_count: 76800 error: "")
compare: (exact: true accepted: true different_pixels: 0 match_pct_10000: 10000)
```

**html_compat spec suite (test/03_system/gui/wm_compare/html_compat_spec.spl):**
- 18 tests passed, 0 failed, duration ≈ 4.4s

**Full wm_compare spec suite (18 files):**
- Passed: 173, Failed: 8 (all 8 in `golden_gate_spec.spl` — pre-existing framebuffer
  baseline drift unrelated to this bug)
- `html_compat_spec.spl`: PASS
- `html_compat_geometry_probe_spec.spl`: PASS

**Root cause (confirmed):** Not an HTML tokenizer/parser hang. The original
timeout was in child runtime discovery — `bin/simple` symlink pointed to an
arch-specific binary that did not exist in clean worktrees, so the harness
fell through to `/usr/bin/env` (not a Simple binary) and timed out waiting
for its `--version` probe. The fix in `html_compat_part1.spl` probes each
candidate with a 2s `rt_process_run_timeout` `--version` call and returns `""`
(fail-fast) when no candidate passes.
