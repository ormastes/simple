# O0/O1 source-revision contract spec asserted the wrong process exit code

- **Filed:** 2026-08-07 (T9, `render_perf_replan_parallel_teams_2026-08-07.md`)
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Component:** `test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl`

## Summary

`gui_showcase_perf_source_revision_contract_spec.spl` (both `it` blocks) asserted
`expect(code).to_equal(0)` on the exit code of
`scripts/check/check-gui-renderdoc-feature-coverage-status.shs`, run against a
synthetic environment that only populates the 4K/8K retained-perf evidence row
under test. That wrapper is a whole-repo aggregate completion gate
(`scripts/check/check-gui-renderdoc-feature-coverage-status.shs:4550-4552`:
`if [ "$status" = "fail" ]; then exit 1; fi`) that fails non-zero whenever ANY
of its many unrelated evidence categories (widget-kind HTML-renderer coverage,
Electron layout-manifest traceability, etc.) is incomplete — which a synthetic
fixture populating only the 4K/8K row always leaves incomplete. That is correct
behavior of the aggregate gate, not a defect. The spec's own acceptance
criteria (see its docstring) is entirely about `evidence.env` field values, not
the wrapper's overall exit status, and the wrapper writes `evidence.env` before
exiting non-zero.

Net effect: both `it` blocks failed on `expect(code).to_equal(0)` before ever
reaching the real assertions on `evidence.env`, even though the underlying
source-revision freshness mechanism was already working correctly — manually
re-running the exact synthetic 4K fixture and reading `evidence.env` directly
showed `gui_showcase_4k_200fps_status=fail`,
`gui_showcase_4k_200fps_source_revision_status=mismatch`, and
`gui_showcase_4k_200fps_reason=stale-4k-source-revision:mismatch;source=stale123;current=current123`
— exactly the values the spec expects.

## Fix

Dropped the `expect(code).to_equal(0)` assertions from both `it` blocks (the
process exit code is still captured but intentionally unchecked); the specs
now assert only on `evidence.env` content, which is what the docstring's
"Acceptance" and "Evidence Keys" sections actually describe. Added a third
sabotage-control case per O0/O1 acceptance requirement ("each spec has at
least one sabotage case proving it is not vacuous"): a fresh (matching)
source-revision row must NOT be flagged `mismatch` — proving the two positive
cases are sensitive to staleness rather than the gate unconditionally failing.

`gui_web_2d_source_revision_emitters_spec.spl` gained an equivalent sabotage
case: a second explicit `GUI_WEB_2D_SOURCE_REVISION` override must produce a
*different* evidence value, proving the field is not hardcoded to the first
test's literal string.

## Verdict (binary: `bin/release/x86_64-unknown-linux-gnu/simple`, Rust
bootstrap seed, `bin/simple test ... --mode=interpreter`)

- `gui_showcase_perf_source_revision_contract_spec.spl`: **3 examples, 3
  passed, 0 failed** (was 2 examples, 0 passed, 2 failed before this fix).
- `gui_web_2d_source_revision_emitters_spec.spl`: **3 examples, 3 passed, 0
  failed** (was already 2/2 green; a sabotage case was added, still green).

O0/O1 (revisions + property trees source-revision contract family) status:
**DONE.**
