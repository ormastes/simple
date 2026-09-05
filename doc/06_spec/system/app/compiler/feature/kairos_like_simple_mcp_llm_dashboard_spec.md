# kairos_like_simple_mcp_llm_dashboard_spec

> Assistant session store + MCP/dashboard surfaces: identity, timeline, retention, live view, and authenticated rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kairos_like_simple_mcp_llm_dashboard_spec

Assistant session store + MCP/dashboard surfaces: identity, timeline, retention, live view, and authenticated rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Assistant session store + MCP/dashboard surfaces: identity, timeline, retention, live view, and authenticated rendering.

## Scenarios

### KAIROS-like simple mcp and llm dashboard

### REQ-KAIROS-001: session identity and lifecycle

#### create and persist an assistant session with stable identity

- create and persist an assistant session with stable identity
   - Expected: session.session_id equals `assistant-kairos-identity`
   - Expected: session.objective equals `coordinate agents`
   - Expected: assistant_store_list_sessions(root).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        # @req REQ-KAIROS-001
        # @req REQ-KAIROS-002
        # @req REQ-KAIROS-003
        # @req REQ-KAIROS-004
        # @req REQ-KAIROS-005
        # @req REQ-KAIROS-006
        # @req REQ-KAIROS-007
        # @req REQ-KAIROS-008
        # @req REQ-KAIROS-009
        # @req REQ-KAIROS-010
        # @req REQ-KAIROS-011
        # @req REQ-KAIROS-012
    # @req REQ-KAIROS-001
# @req REQ-SSPEC-SYSTEM
step("create and persist an assistant session with stable identity")
val root = test_root("identity")
create_session(root, "assistant-kairos-identity")

val loaded = assistant_store_load_session(root, "assistant-kairos-identity")
match loaded:
    case Some(session):
        expect(session.session_id).to_equal("assistant-kairos-identity")
        expect(session.objective).to_equal("coordinate agents")
    case nil:
        fail("persisted assistant session should load")
# evidence(...): store-return + on-disk listing oracle is the complete evidence surface
expect(assistant_store_list_sessions(root).len()).to_equal(1)  # oracle: exactly one persisted session created
```

</details>

#### allow a paused session to resume with preserved state

- allow a paused session to resume with preserved state
   - Expected: session.state equals `running`
   - Expected: session.last_signal equals `resume`
   - Expected: session.event_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# evidence(...): timeline event-count oracle is the complete evidence surface
# @req REQ-SSPEC-SYSTEM
step("allow a paused session to resume with preserved state")
val root = test_root("resume")
create_session(root, "assistant-kairos-resume")
assistant_store_update_state(root, "assistant-kairos-resume", "paused", "pause")
val resumed = assistant_store_update_state(root, "assistant-kairos-resume", "running", "resume")

match resumed:
    case Some(session):
        expect(session.state).to_equal("running")
        expect(session.last_signal).to_equal("resume")
        expect(session.event_count).to_equal(2)  # oracle: one pause + one resume event
    case nil:
        fail("assistant session should resume")
```

</details>

### REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals

#### record a periodic tick wake reason in the session timeline

- record a periodic tick wake reason in the session timeline
   - Expected: timeline[0].kind equals `tick`
   - Expected: timeline[0].signal equals `tick`
   - Expected: timeline[0].message equals `periodic wake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# evidence(...): timeline reason oracle is the complete evidence surface
# @req REQ-SSPEC-SYSTEM
step("record a periodic tick wake reason in the session timeline")
val root = populated_root("tick", "assistant-kairos-tick")
val timeline = assistant_store_collect_timeline(root, "assistant-kairos-tick", 10, 0)

expect(timeline[0].kind).to_equal("tick")
expect(timeline[0].signal).to_equal("tick")
expect(timeline[0].message).to_equal("periodic wake")
```

</details>

#### record an external signal wakeup with source metadata

- record an external signal wakeup with source metadata
   - Expected: timeline[1].kind equals `signal_event`
   - Expected: timeline[1].signal equals `operator`
   - Expected: timeline[1].source equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("record an external signal wakeup with source metadata")
val root = populated_root("signal", "assistant-kairos-signal")
val timeline = assistant_store_collect_timeline(root, "assistant-kairos-signal", 10, 0)

expect(timeline[1].kind).to_equal("signal_event")
expect(timeline[1].signal).to_equal("operator")
expect(timeline[1].source).to_equal("assistant")
```

</details>

### REQ-KAIROS-004: child-agent delegation

#### track a child task with parent linkage and terminal summary

- track a child task with parent linkage and terminal summary
   - Expected: session.children[0] equals `assistant-child-1`
   - Expected: session.child_tasks[0].session_id equals `assistant-kairos-child`
   - Expected: session.child_tasks[0].status equals `completed`
   - Expected: session.child_tasks[0].result_summary equals `child completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("track a child task with parent linkage and terminal summary")
val root = populated_root("child", "assistant-kairos-child")
val loaded = assistant_store_load_session(root, "assistant-kairos-child")

match loaded:
    case Some(session):
        expect(session.children[0]).to_equal("assistant-child-1")
        expect(session.child_tasks[0].session_id).to_equal("assistant-kairos-child")
        expect(session.child_tasks[0].status).to_equal("completed")
        expect(session.child_tasks[0].result_summary).to_equal("child completed")
    case nil:
        fail("assistant session should include child task")
```

</details>

### REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications

#### produce a compact brief from recent session activity

- produce a compact brief from recent session activity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produce a compact brief from recent session activity")
val root = populated_root("brief", "assistant-kairos-brief")
val brief = assistant_store_session_brief(root, "assistant-kairos-brief")

expect(brief).to_contain("session: assistant-kairos-brief")
expect(brief).to_contain("summary: coordinate agents")
expect(brief).to_contain("timeline events: 3")
expect_internal_absence_hidden(brief)
```

</details>

#### preserve notification decision and delivery status

- preserve notification decision and delivery status
   - Expected: notifications.len() equals `3`
   - Expected: notifications[2].kind equals `child_task`
   - Expected: notifications[2].signal equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserve notification decision and delivery status")
val root = populated_root("notify", "assistant-kairos-notify")
val notifications = assistant_store_collect_notifications(root, "assistant-kairos-notify", 10, 0)

expect(notifications.len()).to_equal(3)  # oracle: three decisions recorded in the scenario
expect(notifications[2].kind).to_equal("child_task")
expect(notifications[2].signal).to_equal("completed")
```

</details>

### REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes

#### support standalone simple mcp control without the dashboard

- support standalone simple mcp control without the dashboard
   - Expected: session.mode equals `proactive`
   - Expected: session.policy equals `bounded`
   - Expected: session.event_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("support standalone simple mcp control without the dashboard")
val root = populated_root("standalone-mcp", "assistant-kairos-mcp")
val loaded = assistant_store_load_session(root, "assistant-kairos-mcp")

match loaded:
    case Some(session):
        expect(session.mode).to_equal("proactive")
        expect(session.policy).to_equal("bounded")
        expect(session.event_count).to_equal(3)  # oracle: three appended events in the scenario
    case nil:
        fail("assistant mcp store should work without dashboard routes")
```

</details>

#### support standalone dashboard replay without live mcp

- support standalone dashboard replay without live mcp
   - Expected: snapshot.mode equals `replay`
   - Expected: view.read_only is true
   - Expected: view.primary_action.route_target equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("support standalone dashboard replay without live mcp")
val root = populated_root("standalone-dashboard", "assistant-kairos-replay")
val snapshot = selected_snapshot(root, "assistant-kairos-replay")
val view = assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 2_000_000, 1_000_000, false)

expect(snapshot.mode).to_equal("replay")
expect(view.read_only).to_equal(true)
expect(view.primary_action.route_target).to_equal("blocked")
```

</details>

### REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode

#### attach dashboard live state without moving source of truth

- attach dashboard live state without moving source of truth
   - Expected: view.mode equals `live`
   - Expected: view.live_controls_enabled is true
   - Expected: view.primary_action.route_target equals `assistant_core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attach dashboard live state without moving source of truth")
val root = populated_root("live", "assistant-kairos-live")
val snapshot = selected_snapshot(root, "assistant-kairos-live")
val view = assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 2_000_100, 2_000_000, true)

expect(view.mode).to_equal("live")
expect(view.live_controls_enabled).to_equal(true)
expect(view.primary_action.route_target).to_equal("assistant_core")
```

</details>

#### expose operator-visible task tree and recent events

- expose operator-visible task tree and recent events


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expose operator-visible task tree and recent events")
val root = populated_root("visible", "assistant-kairos-visible")
val snapshot = selected_snapshot(root, "assistant-kairos-visible")
val live_lines = assistant_dashboard_render_live_view(assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 2_000_100, 2_000_000, true))
val digest_lines = assistant_dashboard_render_digest(assistant_dashboard_digest_from_snapshot(snapshot))

expect(live_lines.join("\n")).to_contain("timeline 3 tasks 1 notifications 3")
expect(digest_lines.join("\n")).to_contain("task_summaries 1")
expect_internal_absence_hidden((live_lines + digest_lines).join("\n"))
```

</details>

### REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention

#### preserve structured failure evidence after a child-task crash

- preserve structured failure evidence after a child-task crash
   - Expected: view.failure_state equals `error`
   - Expected: view.failure_detail equals `child crashed`
   - Expected: view.failure_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserve structured failure evidence after a child-task crash")
val root = test_root("failure")
create_session(root, "assistant-kairos-failure")
append_event(root, "assistant-kairos-failure", "error", "child crashed", "failed", 1000)
val snapshot = selected_snapshot(root, "assistant-kairos-failure")
val view = assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 1_000_100, 1_000_000, true)

expect(view.failure_state).to_equal("error")
expect(view.failure_detail).to_equal("child crashed")
expect(view.failure_count).to_equal(1)  # oracle: one child-task crash recorded
```

</details>

#### apply bounded retention or coalescing under bursty signals

- apply bounded retention or coalescing under bursty signals
   - Expected: durable.status equals `pruned`
   - Expected: durable.dropped_timeline_count equals `3`
   - Expected: projection.backpressure_state equals `backpressure`
   - Expected: projection.coalesced_signal_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("apply bounded retention or coalescing under bursty signals")
val root = test_root("retention")
create_session(root, "assistant-kairos-retention")
var i: i64 = 0
while i < 7:
    append_event(root, "assistant-kairos-retention", "signal", "wake", "operator", i + 1)
    i = i + 1

val durable = assistant_store_prune_session_retention(root, "assistant-kairos-retention", 4, 3)
val snapshot = selected_snapshot(root, "assistant-kairos-retention")
val policy = AssistantDashboardRetentionPolicy(
    max_timeline_events: 3,
    max_notifications: 2,
    coalesce_after_repeats: 2,
    backpressure_after_dropped: 1
)
val projection = assistant_dashboard_retention_projection(snapshot, policy)

expect(durable.status).to_equal("pruned")
expect(durable.dropped_timeline_count).to_equal(3)  # oracle: three timeline entries pruned past the retention bound
expect(projection.backpressure_state).to_equal("backpressure")
expect(projection.coalesced_signal_count).to_equal(1)  # oracle: burst of like signals coalesced into one
expect_internal_absence_hidden(projection.notice)
```

</details>

### absence-safe web route contract

#### render authenticated /agents without internal absence markers

- render authenticated /agents without internal absence markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render authenticated /agents without internal absence markers")
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agents", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("selected session unavailable")
expect_internal_absence_hidden(response)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-KAIROS-001`
- `REQ-KAIROS-002`
- `REQ-KAIROS-003`
- `REQ-KAIROS-004`
- `REQ-KAIROS-005`
- `REQ-KAIROS-006`
- `REQ-KAIROS-007`
- `REQ-KAIROS-008`
- `REQ-KAIROS-009`
- `REQ-KAIROS-010`
- `REQ-KAIROS-011`
- `REQ-KAIROS-012`
- `REQ-KAIROS-003:`
- `REQ-KAIROS-006:`
- `REQ-KAIROS-008:`
- `REQ-KAIROS-010:`
- `REQ-KAIROS-012:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ee9c1dd380d2ed92af2f357f1a36fa4d0a2e9b2595d5e99d78eec11081af2f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ee9c1dd380d2ed92af2f357f1a36fa4d0a2e9b2595d5e99d78eec11081af2f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ee9c1dd380d2ed92af2f357f1a36fa4d0a2e9b2595d5e99d78eec11081af2f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl
mirror: doc/06_spec/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'record an external signal wakeup with source metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'track a child task with parent linkage and terminal summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produce a compact brief from recent session activity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
