# Changelog Specification

> 1. expect log size

<!-- sdn-diagram:id=changelog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=changelog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

changelog_spec -> std
changelog_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=changelog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Changelog Specification

## Scenarios

### ChangeLog

#### creates empty changelog

1. expect log size
2. expect log is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = new_changelog(10)
expect log.size() to_equal 0
expect log.is_empty() to_equal true
```

</details>

#### pushes and retrieves events

1. log push
2. log push
3. expect log size
4. expect log is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
log.push(LifecycleEvent.Focus(widget_id: "w1"))
expect log.size() to_equal 2
expect log.is_empty() to_equal false
```

</details>

#### drops oldest when at capacity

1. log push
2. log push
3. log push
4. log push
5. expect log size


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. log push
2. log push
3. log push
4. expect recent len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. log push
2. log push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "btn1"))
log.push(LifecycleEvent.Update(widget_id: "btn1", prop_key: "text", prop_value: "Click"))
val descs = log.recent_descriptions(2)
expect descs[0] to_equal "mount:btn1"
expect descs[1] to_equal "update:btn1.text=Click"
```

</details>

#### clears all events

1. log push
2. log clear
3. expect log size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = new_changelog(10)
log.push(LifecycleEvent.Mount(widget_id: "w1"))
log.clear()
expect log.size() to_equal 0
```

</details>

#### push_all adds multiple events

1. LifecycleEvent Mount
2. LifecycleEvent Mount
3. log push all
4. expect log size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. log push
2. expect recent len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui/changelog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
