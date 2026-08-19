# effect_engine_compare_spec / glass_pipeline_screenshot_spec exceed even a 1800s SOLO run

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
