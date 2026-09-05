# Claude Full Ink Event

> Mirrors the base Ink `Event` propagation flag used by terminal event classes.

<!-- sdn-diagram:id=event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_spec -> std
event_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink Event

Mirrors the base Ink `Event` propagation flag used by terminal event classes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/event_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the base Ink `Event` propagation flag used by terminal event classes.

## Scenarios

### Claude full Ink Event

#### should start with immediate propagation enabled and stop it on request

- Create the base event
   - Expected: event.didStopImmediatePropagation() is false
- Stop immediate propagation
- event stopImmediatePropagation
   - Expected: event.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create the base event")
val event = eventNew()
expect(event.didStopImmediatePropagation()).to_equal(false)

step("Stop immediate propagation")
event.stopImmediatePropagation()
expect(event.didStopImmediatePropagation()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
