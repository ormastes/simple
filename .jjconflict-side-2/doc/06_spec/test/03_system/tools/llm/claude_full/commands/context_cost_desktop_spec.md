# Claude Full Context, Cost, Moved Plugin, and Desktop Commands

> Checks modern SSpec parity for the small descriptor command cluster.

<!-- sdn-diagram:id=context_cost_desktop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_cost_desktop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_cost_desktop_spec -> std
context_cost_desktop_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_cost_desktop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Context, Cost, Moved Plugin, and Desktop Commands

Checks modern SSpec parity for the small descriptor command cluster.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/context_cost_desktop_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the small descriptor command cluster.

## Scenarios

### Claude full context cost desktop commands

#### should model context command rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val usage = ContextUsage.new(8500, 10000, 5000, 2000, 1500)
expect(contextCommand(true).name).to_equal("context")
expect(renderContextCommand(usage).percentText).to_equal("85%")
expect(renderContextCommand(usage).status).to_equal("warning")
expect(renderContextCommand(usage).detail).to_contain("transcript=5000")
```

</details>

#### should model cost and moved-plugin commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(costCommand(true).description).to_contain("cost")
expect(formatCostCents(1234)).to_equal("$12.34")
val moved = createMovedToPluginCommand("review", "Review code", "reviewer", ["rv"])
expect(movedToPluginAliasCount(moved)).to_equal(1)
expect(runMovedToPluginCommand(moved).message).to_contain("/plugin install reviewer")
```

</details>

#### should expose debug and desktop command descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(debugToolCallCommandName()).to_equal("debug-tool-call")
expect(desktopCommandTarget()).to_equal("desktop")
expect(desktopCommand().description).to_contain("desktop")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contextCommandSourceLinesModeled()).to_equal(63)
expect(contextIndexSourceLinesModeled()).to_equal(24)
expect(costCommandSourceLinesModeled()).to_equal(24)
expect(costIndexSourceLinesModeled()).to_equal(23)
expect(movedToPluginSourceLinesModeled()).to_equal(65)
expect(desktopCommandSourceLinesModeled()).to_equal(8)
expect(desktopIndexSourceLinesModeled()).to_equal(26)
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
