# mock_direct_spec

> Feature: Direct Mock Import

<!-- sdn-diagram:id=mock_direct_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mock_direct_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mock_direct_spec -> spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mock_direct_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mock_direct_spec

Feature: Direct Mock Import

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/mock_direct_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Direct Mock Import
Category: Mocking Framework
Status: Complete

## Scenarios

### Direct Mock Import

#### can call CallRecorder.new directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.new()
expect(recorder.calls.len() == 0)
```

</details>

#### records calls on the local harness

1. recorder record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = CallRecorder.new()
recorder.record("ping")
expect(recorder.calls.len() == 1)
expect(recorder.calls[0] == "ping")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
