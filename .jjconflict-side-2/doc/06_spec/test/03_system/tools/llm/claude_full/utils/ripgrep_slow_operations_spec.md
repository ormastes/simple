# Claude Full Ripgrep And Slow Operations

> Focused parity checks for `RipgrepTimeoutError` and `AntSlowLogger`.

<!-- sdn-diagram:id=ripgrep_slow_operations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ripgrep_slow_operations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ripgrep_slow_operations_spec -> std
ripgrep_slow_operations_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ripgrep_slow_operations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ripgrep And Slow Operations

Focused parity checks for `RipgrepTimeoutError` and `AntSlowLogger`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/ripgrep_slow_operations_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parity checks for `RipgrepTimeoutError` and `AntSlowLogger`.

## Scenarios

### Claude full ripgrep and slow operations

#### preserves ripgrep timeout partial results

- Create the custom timeout error and inspect TS-compatible fields
   - Expected: err.name equals `RipgrepTimeoutError`
   - Expected: err.message equals `rg timed out`
   - Expected: err.partialResults equals `["one", "two"]`
   - Expected: isEagainError("spawn failed: os error 11") is true
   - Expected: isEagainError("Resource temporarily unavailable") is true
   - Expected: stripCR("a\r\nb") equals `a\nb`
   - Expected: ripgrepSourceLinesModeled() equals `679`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create the custom timeout error and inspect TS-compatible fields")
val err = RipgrepTimeoutError.new("rg timed out", ["one", "two"])

expect(err.name).to_equal("RipgrepTimeoutError")
expect(err.message).to_equal("rg timed out")
expect(err.partialResults).to_equal(["one", "two"])
expect(isEagainError("spawn failed: os error 11")).to_equal(true)
expect(isEagainError("Resource temporarily unavailable")).to_equal(true)
expect(stripCR("a\r\nb")).to_equal("a\nb")
expect(ripgrepSourceLinesModeled()).to_equal(679)
```

</details>

#### logs ant slow operations only above threshold

- Build a lazy template description after the operation crosses the threshold
- ["JSON stringify
- [TemplateValue object
   - Expected: logger.dispose(110.0) is false
   - Expected: logger.loggedOperations.len() equals `0`
   - Expected: logger.dispose(125.5) is true
   - Expected: logger.loggedOperations.len() equals `1`
   - Expected: logger.lastDurationMs() equals `25.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a lazy template description after the operation crosses the threshold")
val logger = slowLoggingAnt(
    100.0,
    ["JSON.stringify(", ", ", ")"],
    [TemplateValue.object(2), TemplateValue.array(3)],
    "Error\n    at slowOperations.ts:101:1\n    at caller.ts:42:7",
    20.0,
)

expect(logger.dispose(110.0)).to_equal(false)
expect(logger.loggedOperations.len()).to_equal(0)
expect(logger.dispose(125.5)).to_equal(true)
expect(logger.loggedOperations.len()).to_equal(1)
expect(logger.lastDescription()).to_contain("JSON.stringify(Object{2 keys}, Array[3])")
expect(logger.lastDescription()).to_contain("caller.ts:42:7")
expect(logger.lastDurationMs()).to_equal(25.5)
```

</details>

#### keeps threshold and external logger behavior simple

- Resolve thresholds and verify external mode does not record a slow operation
   - Expected: slowOperationThresholdMs("5", "production", "external") equals `5.0`
   - Expected: slowOperationThresholdMs("-1", "development", "external") equals `20.0`
   - Expected: slowOperationThresholdMs("", "production", "ant") equals `300.0`
   - Expected: renderTemplateValue(TemplateValue.string("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz")) equals `abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxy... (full value in folded executable source)`
   - Expected: noop.dispose(999.0) is false
   - Expected: noop.disposed is true
   - Expected: slowOperationsSourceLinesModeled() equals `286`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve thresholds and verify external mode does not record a slow operation")
expect(slowOperationThresholdMs("5", "production", "external")).to_equal(5.0)
expect(slowOperationThresholdMs("-1", "development", "external")).to_equal(20.0)
expect(slowOperationThresholdMs("", "production", "ant")).to_equal(300.0)
expect(renderTemplateValue(TemplateValue.string("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"))).to_equal("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzab...")
val noop = slowLoggingExternal()
expect(noop.dispose(999.0)).to_equal(false)
expect(noop.disposed).to_equal(true)
expect(slowOperationsSourceLinesModeled()).to_equal(286)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
