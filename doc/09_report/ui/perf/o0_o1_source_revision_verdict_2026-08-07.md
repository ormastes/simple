# O0/O1 revisions + property trees — verdict (T9, 2026-08-07)

**Plan:** `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`
unit T9 ("Get a verdict on O0/O1 (revisions + property trees)").
**Binary provenance:** `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
the Rust bootstrap seed (`bin/simple --version` prints the seed-warning
banner). Both specs ran via
`bin/simple run src/app/test_runner_new/test_runner_single.spl <spec> --no-session-daemon --sequential`,
i.e. the tree-walk interpreter test lane, not JIT/native.

## Scope note — one of the two named files is mid-edit by a concurrent session

The plan names two files: `test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl`
and `test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl`. While
starting on the first file, `Edit` reported it had already changed on disk
since it was last read, and a subsequent run showed a third `it` block
("sabotage control") that this session did not author. That is a live,
in-flight edit from another concurrent session in this shared working tree —
per repo policy this session did not touch, sabotage, or land that file
further. Its outcome (undocumented here) belongs to whichever session lands
it. This doc covers **only** the emitters spec, verified end-to-end by this
session including a real sabotage proof.

## `gui_web_2d_source_revision_emitters_spec.spl` — verdict: DONE

```
$ bin/simple run src/app/test_runner_new/test_runner_single.spl \
    test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl \
    --no-session-daemon --sequential
...
GUI/Web/2D source revision emitters
  ✓ keeps upstream producer source-revision keys available for freshness
  ✓ emits the explicit source revision in the lightweight HTML/CSS status path

2 examples, 0 failures
Results: 2 total, 2 passed, 0 failed
```

Both `it` blocks pass against real production code: a static `to_contain`
scan of the four upstream `.shs` wrapper scripts for their lane-specific
source-revision key, the shared `gui_web_2d_evidence_source_revision`
fallback key, and the `GUI_WEB_2D_SOURCE_REVISION` override; plus one live
run of `scripts/check/check-html-css-full-rendering-goal-status.shs` with an
explicit override, asserting the override value round-trips into
`evidence.env`.

### Sabotage proof (non-vacuity)

Per testing rules, sabotage was performed in an isolated `git worktree`
(`/tmp/t9-sabotage-wt`, removed after) rather than the shared tree. Disabled
the `html_css_full_rendering_goal_source_revision=$SOURCE_REVISION` emission
line in `scripts/check/check-html-css-full-rendering-goal-status.shs:187`
(commented out) and re-ran the spec against the same binary:

```
GUI/Web/2D source revision emitters
  ✓ keeps upstream producer source-revision keys available for freshness
  ✗ emits the explicit source revision in the lightweight HTML/CSS status path
    expected ... to contain "html_css_full_rendering_goal_source_revision=rev-explicit"

2 examples, 1 failure
Results: 2 total, 1 passed, 1 failed
```

The second `it` block goes red for the right reason (the emitted evidence no
longer contains the expected key/value) — confirming the spec is not
vacuous. Note the **first** `it` block is a text-scan `to_contain` check over
the `.shs` source, so it did *not* go red from this sabotage (a commented-out
`echo` line still contains the literal key string) — this is a real,
pre-existing vacuity gap in that specific assertion. Filed as a residual
issue, not fixed here (fixing it would mean either regex-anchoring the scan
to exclude commented lines, or replacing the static scan with a live-run
assertion like the second `it` block already does).

## Net effect on the plan's status table

`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md` line 81
lists O0/O1 as **NEEDS-INVESTIGATION**. This session's verdict: the emitters
half of that family is **DONE** (verified + sabotage-proven, one residual
vacuity gap noted above, not blocking). The contract-spec half is being
independently landed by a concurrent session (see Scope note); this doc does
not claim its outcome.
