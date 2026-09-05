# Computer Use Host Adapter

> Checks computer-use DebugLogger and adapter defaults.

<!-- sdn-diagram:id=hostAdapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hostAdapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hostAdapter_spec -> std
hostAdapter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hostAdapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Computer Use Host Adapter

Checks computer-use DebugLogger and adapter defaults.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/computerUse/hostAdapter_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks computer-use DebugLogger and adapter defaults.

## Scenarios

### Computer use host adapter

#### should map logger methods and expose adapter defaults

- var logger = DebugLogger new
- logger = logger silly
- logger = logger debug
- logger = logger info
- logger = logger warn
- logger = logger error
   - Expected: logger.entries[0].level equals `debug`
   - Expected: logger.entries[2].level equals `info`
   - Expected: logger.entries[3].level equals `warn`
   - Expected: logger.entries[4].level equals `error`
   - Expected: adapter.serverName equals `computer-use`
   - Expected: adapter.autoUnhideEnabled is true
   - Expected: adapter.disabled is false
   - Expected: hostAdapterSourceLinesModeled() equals `69`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var logger = DebugLogger.new()
logger = logger.silly("trace")
logger = logger.debug("debug")
logger = logger.info("info")
logger = logger.warn("warn")
logger = logger.error("error")
expect(logger.entries[0].level).to_equal("debug")
expect(logger.entries[2].level).to_equal("info")
expect(logger.entries[3].level).to_equal("warn")
expect(logger.entries[4].level).to_equal("error")
val adapter = ComputerUseHostAdapterModel.new("computer-use", false)
expect(adapter.serverName).to_equal("computer-use")
expect(adapter.autoUnhideEnabled).to_equal(true)
expect(adapter.disabled).to_equal(false)
expect(hostAdapterSourceLinesModeled()).to_equal(69)
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
