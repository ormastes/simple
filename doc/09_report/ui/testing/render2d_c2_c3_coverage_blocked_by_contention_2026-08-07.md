# C2/C3 assessment — engine2d GPU + os/compositor closure — 2026-08-07

Plan: `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`
(Unit C2, lines 461-464; Unit C3, lines 466-471). Session context: this session
was briefed that `bin/simple` had "JUST redeployed with all coverage fixes" and
that C2/C3 were "blocked on exactly this deploy." Both halves of that premise
were checked directly against the live binary and the live machine, not assumed.

## Verdict: neither C2 nor C3 produced a trustworthy coverage number this session. No percentage is reported for either unit.

Two independent findings, both re-verified with direct commands:

### 1. The coverage-tooling premise is TRUE but only PARTIALLY — re-verify, don't cite wholesale

`bin/simple spl-coverage status`, `dump`, `rollup`, `clear` all dispatch now
(previously: `file not found: spl-coverage`, per
`doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`).
A live `spl-coverage status` run (no test invocation needed — it read whatever
decision data existed from the binary's own prior self-instrumented run)
produced a real `summary:` block:

```
total_decisions: 30
covered_decisions: 3
total_conditions: 0
covered_conditions: 0
decision_percent: 10.0
condition_percent: 100.0
path_percent: 100.0
```

This is genuine forward progress versus C1's finding (`doc/09_report/ui/testing/
render2d_c1_line_coverage_partial_2026-08-07.md`) of **zero** branch/decision
rows in any artifact — decision rows now exist, with entries like
`224535072, /home/ormastes/dev/pub/simple/src/lib/nogc_async_mut/cli/log_modes.spl, 55, 5, 1, 1`
(real absolute path + real line number).

**But it is a mixed state, not a full fix**: several rows in the same dump still
carry the placeholder `<entry>` instead of a real path (e.g.
`3389716552, <entry>, 240, 13, 0, 1`) — so prereq1 (real source spans) is
partially, not fully, met. And `condition_percent: 100.0` with
`total_conditions: 0` is a vacuous 0/0-forced-to-100 ratio — this directly
confirms the task brief's own stated caveat: **`conditions` rows are not
emitted by the runtime today**; any coverage number in this family must be
labeled `decision`, never `branch`/`condition`.

### 2. C2/C3 target-spec runs could not complete this session — severe shared-box contention, not a C2/C3-specific defect

Every attempt to execute C2's or C3's actual acceptance command timed out,
including a spec that completed cleanly in the prior C1 session:

| command | timeout | result |
|---|---|---|
| `SIMPLE_COVERAGE=1 bin/simple test test/01_unit/lib/nogc_sync_mut/gpu/engine2d/ --no-cache --no-cover-check` | 300s | killed by internal `timeout`, no `Results:` line ever printed, stuck at "Session setup: 10382ms" |
| `simd_isa_provider_spec.spl` alone, `--no-session-daemon --sequential --coverage` | 180s | killed, stuck at "child binary: .../simple" (never entered the test) |
| same spec, matching C1's working invocation pattern (`--coverage`, no extra flags) | 600s | killed, still running |
| **Sanity check — `scalar_oracle_spec.spl`, the exact spec C1 measured cleanly in the prior session (89.6% line coverage, sub-30s)** | 120s | **also killed**, `rc=124` |

The sanity check is the deciding evidence: a spec proven fast in the prior
session now times out too, which rules out "C2/C3's specific files are slow"
and points at the machine. `uptime` at measurement time: `load average: 11.39,
18.49, 18.27` on a 32-core box, with **35 concurrent `bin/simple`/
`target/release/simple` processes** running — including another session's
`bin/simple run src/app/test_runner_new/test_runner_single.spl
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl` racing
the exact same spec file this session was trying to measure. This matches the
repo's documented shared-WC hazard class (concurrent sessions contend for the
same shared box / test daemon / cache).

## What was NOT done, and why no number is fabricated

- No C2 (`src/lib/nogc_sync_mut/gpu/engine2d/`) decision or line percentage is
  reported — no run against that module tree completed.
- No C3 (`src/os/compositor/` engine2d+software+vulkan) decision or line
  percentage is reported — no run was even attempted past confirming which
  spec files exist, given C2's timeouts made a same-session C3 attempt not
  worth the queue time.
- No new spec `it`s were written. Per the plan's own acceptance criteria,
  writing "covers `<fn>` `<condition>` arm" its requires real arm identity from
  a completed run first; fabricating them against no measurement would be
  exactly the fabrication risk `CLAUDE.md` and this repo's bug-tracking
  convention warn against.
- The gate script `scripts/check/check-render2d-coverage.shs` was not edited.

## C3 spec inventory (recorded for the next attempt, not run)

Files with a dedicated spec: `compositor_engine2d.spl` →
`compositor_engine2d_surface_spec.spl`; `engine2d_baremetal_core.spl` →
`engine2d_baremetal_core_parity_spec.spl`; `vulkan_compositor_backend.spl` →
`vulkan_compositor_backend_spec.spl`; `frame_pacer.spl` → `frame_pacer_spec.spl`.
No dedicated spec found for `engine2d_baremetal_rect_core.spl`,
`display_backend_core.spl`, or `dirty_rect.spl` — worth confirming via a full
repo search (only a targeted glob was run this session) before C3's next
attempt.

## Recommendation

Re-run C2/C3's acceptance commands in a pinned, single-tenant worktree (per
`reference_measurement_requires_a_pinned_worktree.md`) or at a time with no
concurrent sessions on this box — 120s is not long enough headroom on a
32-core/load-18 machine for even a previously-fast spec. Re-verify prereq1
(real source spans) specifically for the `<entry>`-placeholder rows before
citing it as fully met.
