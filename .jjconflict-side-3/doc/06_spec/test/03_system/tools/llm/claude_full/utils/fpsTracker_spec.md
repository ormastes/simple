# Claude Full FpsTracker

> Checks FPS metric aggregation.

<!-- sdn-diagram:id=fpsTracker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fpsTracker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fpsTracker_spec -> std
fpsTracker_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fpsTracker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FpsTracker

Checks FPS metric aggregation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks FPS metric aggregation.

## Scenarios

### Claude full FpsTracker

#### should report no metrics until time advances

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FpsTracker.new().getMetrics().averageFpsHundredths).to_equal(0)
```

</details>

#### should compute average and low one percent FPS

- var tracker = FpsTracker new
- tracker = tracker record
- tracker = tracker record
- tracker = tracker record
   - Expected: metrics.averageFpsHundredths equals `1500`
   - Expected: metrics.low1PctFpsHundredths equals `4000`
   - Expected: fpsTrackerSourceLinesModeled() equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tracker = FpsTracker.new()
tracker = tracker.record(16, 100)
tracker = tracker.record(20, 200)
tracker = tracker.record(25, 300)
val metrics = tracker.getMetrics()
expect(metrics.averageFpsHundredths).to_equal(1500)
expect(metrics.low1PctFpsHundredths).to_equal(4000)
expect(fpsTrackerSourceLinesModeled()).to_equal(47)
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
