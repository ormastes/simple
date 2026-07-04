# Assistant Digest Specification

> <details>

<!-- sdn-diagram:id=assistant_digest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_digest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_digest_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_digest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Digest Specification

## Scenarios

### assistant dashboard digest

#### renders digest checkpoint, summary, task summaries, and warnings without internal absence marker

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = assistant_dashboard_digest_from_snapshot(make_snapshot(make_session("session-digest")))
val lines = assistant_dashboard_render_digest(view)
val rendered = lines.join("\n")

expect(view.status).to_equal("ready")
expect(view.checkpoint_id).to_equal("digest-1")
expect(view.summary).to_equal("digest summary")
expect(view.recent_detail).to_equal("recent detail")
expect(view.task_summary_count).to_equal(1)
expect(view.warning_count).to_equal(1)
expect(view.notification_count).to_equal(1)
expect_absence_marker_hidden(rendered)
```

</details>

#### renders missing selected sessions as option-like digest absence

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = AssistantDashboardSnapshot(
    selected_session_id: "missing-session",
    total_sessions: 0,
    sessions: [],
    timeline: [],
    notifications: [],
    source_root: ".build/llm_dashboard/assistant",
    mode: "replay"
)
val view = assistant_dashboard_digest_from_snapshot(snapshot)
val lines = assistant_dashboard_render_digest(view)
val rendered = lines.join("\n")

expect(view.status).to_equal("missing")
expect(view.checkpoint_id).to_equal("none")
expect(view.summary).to_equal("none")
expect_absence_marker_hidden(rendered)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/assistant_digest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant dashboard digest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
