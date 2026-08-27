# Changelog Specification

> Tests covering ChangeLog.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Changelog Specification

## Scenarios

### ChangeLog

#### creates empty changelog

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty changelog


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty changelog")
val log = new_changelog(10)
expect log.size() to_equal 0
expect log.is_empty() to_equal true
```

</details>

#### pushes and retrieves events

- pushes and retrieves events


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes and retrieves events")
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
log.push(LifecycleEvent.Focus(widget_id: "w1"))
expect log.size() to_equal 2
expect log.is_empty() to_equal false
```

</details>

#### drops oldest when at capacity

- drops oldest when at capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops oldest when at capacity")
val log = new_changelog(3)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
log.push(LifecycleEvent.Mount(widget_id: "w2"))
log.push(LifecycleEvent.Mount(widget_id: "w3"))
log.push(LifecycleEvent.Mount(widget_id: "w4"))
expect log.size() to_equal 3
val events = log.all()
# w1 should have been dropped
val first_desc = describe_lifecycle_event(events[0])
expect first_desc to_equal "mount:w2"
```

</details>

#### returns recent N events

- returns recent N events


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns recent N events")
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
log.push(LifecycleEvent.Focus(widget_id: "w2"))
log.push(LifecycleEvent.Blur(widget_id: "w3"))
val recent = log.recent(2)
expect recent.len() to_equal 2
val first_desc = describe_lifecycle_event(recent[0])
expect first_desc to_equal "focus:w2"
```

</details>

#### returns human-readable descriptions

- returns human-readable descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns human-readable descriptions")
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "btn1"))
log.push(LifecycleEvent.Update(widget_id: "btn1", prop_key: "text", prop_value: "Click"))
val descs = log.recent_descriptions(2)
expect descs[0] to_equal "mount:btn1"
expect descs[1] to_equal "update:btn1.text=Click"
```

</details>

#### clears all events

- clears all events


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all events")
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
log.clear()
expect log.size() to_equal 0
```

</details>

#### push_all adds multiple events

- push_all adds multiple events


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_all adds multiple events")
val log = new_changelog(10)
val events: [LifecycleEvent] = [
    LifecycleEvent.Mount(widget_id: "a"),
    LifecycleEvent.Mount(widget_id: "b")
]
log.push_all(events)
expect log.size() to_equal 2
```

</details>

#### returns all when recent count exceeds size

- returns all when recent count exceeds size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all when recent count exceeds size")
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
val recent = log.recent(100)
expect recent.len() to_equal 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/changelog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ChangeLog.
- ChangeLog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `e959ece65ee29ef2644671b5c3c864dc6e66cee89f69850949d7cb92b7fa394f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e959ece65ee29ef2644671b5c3c864dc6e66cee89f69850949d7cb92b7fa394f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e959ece65ee29ef2644671b5c3c864dc6e66cee89f69850949d7cb92b7fa394f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/changelog_spec.spl
mirror: doc/06_spec/unit/app/ui/changelog_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/changelog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/changelog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/changelog_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty changelog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/changelog_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes and retrieves events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/changelog_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops oldest when at capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
