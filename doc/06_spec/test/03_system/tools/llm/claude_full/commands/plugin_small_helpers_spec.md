# Claude Full Plugin Small Helpers

> Checks modern SSpec parity for small plugin helpers.

<!-- sdn-diagram:id=plugin_small_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_small_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_small_helpers_spec -> std
plugin_small_helpers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_small_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Small Helpers

Checks modern SSpec parity for small plugin helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_small_helpers_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for small plugin helpers.

## Scenarios

### Claude full plugin small helpers

#### should parse plugin args and expose command names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pluginIndexCommandName()).to_equal("plugin")
expect(pluginCommandName()).to_equal("plugin")
val args = parsePluginArgs("install foo --trust")
expect(args.action).to_equal("install")
expect(args.target).to_equal("foo")
expect(pluginArgsHasFlag(args, "--trust")).to_equal(true)
```

</details>

#### should format details errors options and validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val details = PluginDetails.new("p", "1.0.0", "desc", true)
expect(pluginDetailsSummary(details)).to_contain("trusted")
expect(pluginErrorView("network", "down").recoverable).to_equal(true)
expect(choosePluginOption(startPluginOptionsFlow(), "enabled").step).to_equal("confirm")
expect(pluginTrustWarningMessage("p")).to_contain("Trust")
expect(validatePluginName("bad name")).to_equal("invalid-name")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pluginIndexSourceLinesModeled()).to_equal(10)
expect(parseArgsSourceLinesModeled()).to_equal(103)
expect(pluginDetailsHelpersSourceLinesModeled()).to_equal(116)
expect(pluginErrorsSourceLinesModeled()).to_equal(123)
expect(pluginOptionsFlowSourceLinesModeled()).to_equal(134)
expect(pluginTrustWarningSourceLinesModeled()).to_equal(31)
expect(validatePluginSourceLinesModeled()).to_equal(97)
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
