# Assistant Live View Specification

> Tests covering assistant dashboard live view.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Live View Specification

## Scenarios

### assistant dashboard live view

#### renders replay snapshots as read-only without internal absence marker text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders replay snapshots as read-only without internal absence marker text
   - Expected: view.read_only is true
   - Expected: view.live_controls_enabled is false
   - Expected: view.primary_action.route_target equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders replay snapshots as read-only without internal absence marker text")
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_session("session-replay", 1000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 2_000_000, 1_000_000, false)
val lines = assistant_dashboard_render_live_view(view)
val rendered = lines.join("\n")

expect(view.read_only).to_equal(true)
expect(view.live_controls_enabled).to_equal(false)
expect(view.primary_action.route_target).to_equal("blocked")
expect_absence_marker_hidden(rendered)
expect(rendered).to_contain("replay snapshot is read-only")
```

</details>

#### routes fresh live snapshots to assistant_core and exposes task counts

- routes fresh live snapshots to assistant_core and exposes task counts
   - Expected: view.read_only is false
   - Expected: view.live_controls_enabled is true
   - Expected: view.freshness_state equals `fresh`
   - Expected: view.task_count equals `1`
   - Expected: view.primary_action.allowed is true
   - Expected: view.primary_action.route_target equals `assistant_core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes fresh live snapshots to assistant_core and exposes task counts")
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_session("session-live", 2000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 2_000_100, 2_000_000, true)

expect(view.read_only).to_equal(false)
expect(view.live_controls_enabled).to_equal(true)
expect(view.freshness_state).to_equal("fresh")
expect(view.task_count).to_equal(1)
expect(view.primary_action.allowed).to_equal(true)
expect(view.primary_action.route_target).to_equal("assistant_core")
```

</details>

#### blocks stale live snapshots and asks the operator to refresh

- blocks stale live snapshots and asks the operator to refresh
   - Expected: view.read_only is true
   - Expected: view.live_controls_enabled is false
   - Expected: view.freshness_state equals `stale`
   - Expected: view.primary_action.allowed is false
   - Expected: view.failure_state equals `bridge_stale`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("blocks stale live snapshots and asks the operator to refresh")
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_session("session-stale", 3000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 50_000_000, 1_000_000, true)
val lines = assistant_dashboard_render_live_view(view)

expect(view.read_only).to_equal(true)
expect(view.live_controls_enabled).to_equal(false)
expect(view.freshness_state).to_equal("stale")
expect(view.primary_action.allowed).to_equal(false)
expect(view.failure_state).to_equal("bridge_stale")
expect(lines.join("\n")).to_contain("refresh required before operator actions")
```

</details>

#### renders assistant crash evidence from failed session metadata

- renders assistant crash evidence from failed session metadata
   - Expected: view.failure_state equals `error`
   - Expected: view.failure_count equals `1`
   - Expected: view.failure_detail equals `model process crashed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders assistant crash evidence from failed session metadata")
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_failed_session("session-crash", 4000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 4_000_100, 4_000_000, true)
val lines = assistant_dashboard_render_live_view(view)
val rendered = lines.join("\n")

expect(view.failure_state).to_equal("error")
expect(view.failure_count).to_equal(1)
expect(view.failure_detail).to_equal("model process crashed")
expect(rendered).to_contain("failure error model process crashed")
expect_absence_marker_hidden(rendered)
```

</details>

#### renders missing selected-session evidence without internal absence marker text

- renders missing selected-session evidence without internal absence marker text
   - Expected: view.failure_state equals `missing`
   - Expected: view.failure_detail equals `selected session unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders missing selected-session evidence without internal absence marker text")
val policy = assistant_bridge_default_policy()
val snapshot = AssistantDashboardSnapshot(
    selected_session_id: "missing-session",
    total_sessions: 0,
    sessions: [],
    timeline: [],
    notifications: [],
    source_root: ".build/llm_dashboard/assistant",
    mode: "replay"
)
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 1_000_000, 1_000_000, false)
val lines = assistant_dashboard_render_live_view(view)
val rendered = lines.join("\n")

expect(view.failure_state).to_equal("missing")
expect(view.failure_detail).to_equal("selected session unavailable")
expect_absence_marker_hidden(rendered)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering assistant dashboard live view.
- assistant dashboard live view

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09996a6b5f3032e4fff7d193b89efd5ddb514b5acd4e4464330d34ca3f7a1cd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09996a6b5f3032e4fff7d193b89efd5ddb514b5acd4e4464330d34ca3f7a1cd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09996a6b5f3032e4fff7d193b89efd5ddb514b5acd4e4464330d34ca3f7a1cd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl
mirror: doc/06_spec/01_unit/app/llm_dashboard/assistant_live_view_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_dashboard/assistant_live_view_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_dashboard/assistant_live_view_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders replay snapshots as read-only without internal absence marker text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes fresh live snapshots to assistant_core and exposes task counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks stale live snapshots and asks the operator to refresh' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
