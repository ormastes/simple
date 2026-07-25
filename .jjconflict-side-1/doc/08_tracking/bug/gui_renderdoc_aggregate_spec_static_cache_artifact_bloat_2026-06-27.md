# Bug: GUI RenderDoc aggregate spec multiplies cached gate artifacts

**Status:** mitigated

**Area:** GUI/web RenderDoc aggregate status, SPipe system test resources

## Symptom

Running `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
under the interpreter is resource-heavy enough to risk Codex/session
interruption. The spec has 33 scenarios and most scenarios shell out to
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.

After an interrupted aggregate run, build output showed many per-scenario
directories at roughly 15 MB each:

- `build/test-gui-renderdoc-feature-coverage-status-8k`
- `build/test-gui-renderdoc-feature-coverage-status-4k`
- `build/test-gui-renderdoc-feature-coverage-status-strict`
- other synthetic negative-case directories

No live `simple test` or aggregate checker process remained after the
interruption, so the observed risk is artifact and process lifetime pressure
rather than a still-running runaway process.

## Cause

`run_nested_gate(..., static_cache=True)` served cached nested gate results by
recursively copying the whole cache tree into each scenario's aggregate build
directory. The static cache itself was about 15 MB, and each synthetic scenario
materialized another full copy even when the aggregate checker only needed the
top-level `evidence.env` text and report path.

This multiplied disk IO and artifact volume across 33 interpreted scenarios,
which increases crash/session-loss risk and makes broad reruns expensive.

## Mitigation

`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` now materializes
only `evidence.env` and `report.md` from a static cached nested gate into the
scenario target directory. Fresh cache population remains unchanged.

The checker also supports `GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0` to suppress the
large raw evidence stdout stream. The aggregate SPipe spec uses this mode
because every scenario already reads `evidence.env` from disk and does not need
to retain the raw stdout string in the test runner.

## Verification

- `sh -n scripts/check/check-gui-renderdoc-feature-coverage-status.shs` passed.
- One checker invocation with `GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR` reused
  the existing static cache and completed in 18 seconds.
- The resulting aggregate directory was 340 KB and contained only top-level
  nested gate `evidence.env` / `report.md` files, instead of recursive cached
  gate trees near 15 MB per synthetic scenario.
- A quiet-mode checker invocation completed without printing the raw evidence
  env to stdout.
- The 33-scenario interpreted aggregate spec was intentionally not rerun in this
  session to avoid repeating the crash-prone broad path.

## Follow-Up

- Keep avoiding repeated full runs of
  `gui_renderdoc_feature_coverage_status_spec.spl` in one Codex session.
- If more pressure appears, split the aggregate spec into smaller focused specs
  or add a checker self-test for static-cache reuse without invoking all 33
  scenarios.
- The older `simple_test_runner_memory_leak_2026-06-14.md` runner leak still
  applies to very large interpreted test sessions.
