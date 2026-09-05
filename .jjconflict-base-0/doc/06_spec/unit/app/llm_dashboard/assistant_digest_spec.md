# Assistant Digest Specification

> Tests covering assistant dashboard digest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Digest Specification

## Scenarios

### assistant dashboard digest

#### renders digest checkpoint, summary, task summaries, and warnings without internal absence marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders digest checkpoint, summary, task summaries, and warnings without internal absence marker
   - Expected: view.status equals `ready`
   - Expected: view.checkpoint_id equals `digest-1`
   - Expected: view.summary equals `digest summary`
   - Expected: view.recent_detail equals `recent detail`
   - Expected: view.task_summary_count equals `1`
   - Expected: view.warning_count equals `1`
   - Expected: view.notification_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders digest checkpoint, summary, task summaries, and warnings without internal absence marker")
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

- renders missing selected sessions as option-like digest absence
   - Expected: view.status equals `missing`
   - Expected: view.checkpoint_id equals `none`
   - Expected: view.summary equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders missing selected sessions as option-like digest absence")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering assistant dashboard digest.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e8d159aa7d71649c74b5c17f62e0ee3fb01f0dbc944eb0c9ec0206acdb1efdc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8d159aa7d71649c74b5c17f62e0ee3fb01f0dbc944eb0c9ec0206acdb1efdc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8d159aa7d71649c74b5c17f62e0ee3fb01f0dbc944eb0c9ec0206acdb1efdc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/llm_dashboard/assistant_digest_spec.spl
mirror: doc/06_spec/unit/app/llm_dashboard/assistant_digest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_dashboard/assistant_digest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_dashboard/assistant_digest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_dashboard/assistant_digest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_dashboard/assistant_digest_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders digest checkpoint, summary, task summaries, and warnings without internal absence marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/assistant_digest_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders missing selected sessions as option-like digest absence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
