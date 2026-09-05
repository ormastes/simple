# Claude Full Task Output and Telemetry

> Checks modern SSpec parity for task output and BigQuery metrics export.

<!-- sdn-diagram:id=task_telemetry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_telemetry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_telemetry_spec -> std
task_telemetry_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_telemetry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Task Output and Telemetry

Checks modern SSpec parity for task output and BigQuery metrics export.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/task_telemetry_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for task output and BigQuery metrics export.

## Scenarios

### Claude full task output and telemetry

#### should model pipe task output buffering

- var output = TaskOutput new
- output = output writeStdout
   - Expected: output.path equals `/tmp/tasks/task-a.output`
   - Expected: output.totalLinesValue equals `2`
   - Expected: output.getStdout(5) equals `world`
   - Expected: output.getStderr() equals `warn`
- output = output writeStdout
   - Expected: output.diskEnabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var output = TaskOutput.new("task-a", "/tmp/tasks", false, 20)
output = output.writeStdout("hello\nworld").writeStderr("warn")
expect(output.path).to_equal("/tmp/tasks/task-a.output")
expect(output.totalLinesValue).to_equal(2)
expect(output.getStdout(5)).to_equal("world")
expect(output.getStderr()).to_equal("warn")
output = output.writeStdout(" this line is too long")
expect(output.diskEnabled).to_equal(true)
```

</details>

#### should model file polling progress

- var output = TaskOutput new
- output = output startPolling
   - Expected: output.polling is true
   - Expected: output.progressEvents.len() equals `1`
   - Expected: output.getStderr() equals ``
   - Expected: output.stopPolling().polling is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var output = TaskOutput.new("task-b", "/tmp/tasks", true, DEFAULT_MAX_MEMORY)
output = output.startPolling().tickTail("a\nb\nc\nd\ne\nf", 12)
expect(output.polling).to_equal(true)
expect(output.progressEvents.len()).to_equal(1)
expect(output.progressEvents[0].lastLines).to_contain("b")
expect(output.getStderr()).to_equal("")
expect(output.stopPolling().polling).to_equal(false)
```

</details>

#### should model BigQuery metrics export decisions

- var exporter = BigQueryMetricsExporter new
   - Expected: exporter.endpoint equals `https://metrics.example/api/claude_code/metrics`
   - Expected: skipped.code equals `EXPORT_SUCCESS`
   - Expected: skipped.note equals `trust not established`
   - Expected: failed.code equals `EXPORT_FAILED`
   - Expected: sent.payload.metrics[0].name equals `requests`
   - Expected: sent.payload.resourceAttributes[3].value equals `claude_ai`
   - Expected: exporter.shutdownExporter().export(true, true, "", true, "requests", 1).error equals `Exporter has been shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exporter = BigQueryMetricsExporter.new(0, "ant", "https://metrics.example")
expect(exporter.endpoint).to_equal("https://metrics.example/api/claude_code/metrics")
val skipped = exporter.export(true, false, "", true, "requests", 7)
expect(skipped.code).to_equal(EXPORT_SUCCESS)
expect(skipped.note).to_equal("trust not established")
val failed = exporter.export(true, true, "missing auth", true, "requests", 7)
expect(failed.code).to_equal(EXPORT_FAILED)
val sent = exporter.export(true, true, "", true, "requests", 7)
expect(sent.payload.metrics[0].name).to_equal("requests")
expect(sent.payload.resourceAttributes[3].value).to_equal("claude_ai")
expect(exporter.shutdownExporter().export(true, true, "", true, "requests", 1).error).to_equal("Exporter has been shutdown")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(taskOutputSourceLinesModeled()).to_equal(390)
expect(bigQueryExporterSourceLinesModeled()).to_equal(252)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
