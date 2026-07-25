# Claude Full Plugin Dialog And Cell Medium Files

> Checks focused model parity for the plugin options dialog and installed cell.

<!-- sdn-diagram:id=plugin_dialog_cell_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_dialog_cell_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_dialog_cell_spec -> std
plugin_dialog_cell_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_dialog_cell_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Plugin Dialog And Cell Medium Files

Checks focused model parity for the plugin options dialog and installed cell.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/plugin_dialog_cell_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks focused model parity for the plugin options dialog and installed cell.

## Scenarios

### Claude full plugin dialog and installed cell medium files

#### should build final option values with defaults and masked secret rows

- PluginOptionField new
- PluginOptionField new
   - Expected: model.title equals `Configure review`
   - Expected: model.focusedName equals `apiKey`
   - Expected: model.canSave is true
   - Expected: model.finalValues[0] equals `apiKey=secret-token`
   - Expected: model.finalValues[1] equals `mode=fast`
   - Expected: pluginOptionsDialogSubmit(PluginOptionsDialogProps.new("review", fields, 0, false, "")) equals `save:review`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    PluginOptionField.new("apiKey", "API key", "", "secret-token", true, true),
    PluginOptionField.new("mode", "Mode", "fast", "", false, false),
]
val model = PluginOptionsDialog(PluginOptionsDialogProps.new("review", fields, 0, false, ""))
expect(model.title).to_equal("Configure review")
expect(model.focusedName).to_equal("apiKey")
expect(model.canSave).to_equal(true)
expect(model.rows[0]).to_contain("********")
expect(model.finalValues[0]).to_equal("apiKey=secret-token")
expect(model.finalValues[1]).to_equal("mode=fast")
expect(pluginOptionsDialogSubmit(PluginOptionsDialogProps.new("review", fields, 0, false, ""))).to_equal("save:review")
```

</details>

#### should block saves when required options are missing or saving

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = [PluginOptionField.new("token", "Token", "", "", true, true)]
val missingModel = PluginOptionsDialog(PluginOptionsDialogProps.new("deploy", missing, 0, false, ""))
expect(missingModel.canSave).to_equal(false)
expect(missingModel.errorMessage).to_contain("Missing required option: token")
val savingModel = PluginOptionsDialog(PluginOptionsDialogProps.new("deploy", missing, 0, true, "Still saving"))
expect(savingModel.saveLabel).to_equal("Saving...")
expect(savingModel.errorMessage).to_equal("Still saving")
```

</details>

#### should render installed cells with status, actions, and expanded details

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val props = UnifiedInstalledCellProps.new("review@core", "review", "core", "Review code", true, true, true, true, false, true, "1.0.0", "1.1.0", "", ["review", "fix"])
val cell = UnifiedInstalledCell(props)
expect(cell.marker).to_equal(">")
expect(cell.status).to_equal("update available")
expect(cell.subtitle).to_equal("core 1.0.0")
expect(cell.actions[0]).to_equal("update")
expect(cell.actions).to_contain("disable")
expect(cell.details).to_contain("commands: review, fix")
expect(cell.details).to_contain("latest: 1.1.0")
```

</details>

#### should render disabled and error cell actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val disabled = UnifiedInstalledCell(UnifiedInstalledCellProps.new("lint@local", "lint", "local", "Lint", false, false, false, true, true, false, "", "", "", []))
expect(disabled.status).to_equal("disabled")
expect(disabled.subtitle).to_equal("local")
expect(disabled.actions[0]).to_equal("enable")

val errored = UnifiedInstalledCell(UnifiedInstalledCellProps.new("bad@core", "bad", "core", "Broken", true, false, true, true, false, false, "1.0.0", "", "load failed", []))
expect(errored.status).to_equal("error")
expect(errored.actions).to_equal(["details", "remove"])
expect(errored.details).to_contain("error: load failed")
```

</details>

#### should preserve source line floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pluginOptionsDialogSourceLinesModeled()).to_equal(356)
expect(unifiedInstalledCellSourceLinesModeled()).to_equal(564)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
