# effect_engine_compare_spec / glass_pipeline_screenshot_spec exceed even a 1800s SOLO run
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-08-19
- Status: OPEN (perf, slow-not-hung — proven)
- Binary: `bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple` (deployed seed, 2026-08-19)

## Evidence

- `SIMPLE_TIMEOUT_SECONDS=3600 timeout 1800 bin/simple test test/02_integration/rendering/effect_engine_compare_spec.spl`
  → rc=124 (killed at 1800s), zero per-example output. Identical for
  `glass_pipeline_screenshot_spec.spl`.
- Slow-not-hung proof: a probe spec running the same
  `capture_with_backend`/`capture_with_effect_engine` on the same
  `generate_glass_test_html("glass_dark")` page at **40x30** completes and
  passes (success=true, 1200 px) in ~14 min wall including startup.
  The real specs use **400x300** (100x the pixels) with 2 captures per example
  and 4-5 examples per spec — hours per spec at current per-pixel cost.

## Why

The glass test page (50 KB HTML) is rendered through the pure-Simple layout +
software rasterizer, which currently executes in the interpreter on this
binary. Per-pixel effect-engine cost dominates; nothing is stuck (the tiny run
proves forward progress and correct output).

## Actions taken

- `# @timeout_secs 2400` headers added to both specs (runner supports the
  directive; parsed in `test_runner_main.spl` / `test_runner_single.spl` /
  `test_runner_client.spl`) so suite runs classify them by budget instead of
  the 120s default — note 2400s is still NOT enough at 400x300 today; the
  annotation removes false TOUT noise for the browser_session specs and keeps
  these two honestly red-by-budget rather than mystery-TOUT.

## Fix options (not taken unilaterally)

1. Deploy a JIT/native-compiled rendering path for the capture pipeline
   (preferred; cost drops orders of magnitude).
2. Reduce spec capture size (e.g. 100x75) — weakens pixel-diff coverage;
   needs owner approval.


## Triage addendum (2026-11-11, lane ne7)

**Status: LIVE — remains OPEN; out of scope for a P3 traverse lane.**

Re-checked on release/1.0.0 tip (branch work/p3-ne7-20261111):

- `test/02_integration/rendering/effect_engine_compare_spec.spl` still
  captures at 400x300 (`val W: i32 = 400`, `val H: i32 = 300`) with two
  `capture_with_effect_engine` calls per example; `glass_pipeline_screenshot_spec.spl`
  unchanged in shape.
- The `@timeout_secs 2400` mitigation this doc says was applied is NOT present
  in the release tip — `git log -S "timeout_secs 2400"` over the file's full
  history on this branch returns no commit.
- No JIT/native capture path for the pure-Simple layout + software rasterizer
  pipeline has been deployed; `capture_with_effect_engine`
  (`src/lib/gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl:132`)
  still renders through the software backend (the 2026-10-27 v3 triage freeze
  measured that both "int" and "float" engine names call the same software
  backend after validation).
- 2026-10-27 v3 freeze classification: `valid / untested / keep_open`; the
  documented fix options (deploy JIT rendering path, or shrink capture size)
  were explicitly "not taken unilaterally" and still require an owner
  decision.

Not re-run here: at 400x300 the spec needs hours of interpreter raster time;
no honest PASS/FAIL is obtainable in a P3 lane. Remaining owner decision is
unchanged: deploy a JIT/native capture path or approve a capture-size
reduction.
