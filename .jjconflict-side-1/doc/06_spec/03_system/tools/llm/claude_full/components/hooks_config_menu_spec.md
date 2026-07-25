# Claude Full HooksConfigMenu Component

> Checks hook rows, enable-disable state, filters, prompt dialogs, summaries, validation, and loading/error/empty states.

<!-- sdn-diagram:id=hooks_config_menu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hooks_config_menu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hooks_config_menu_spec -> std
hooks_config_menu_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hooks_config_menu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full HooksConfigMenu Component

Checks hook rows, enable-disable state, filters, prompt dialogs, summaries, validation, and loading/error/empty states.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks hook rows, enable-disable state, filters, prompt dialogs, summaries, validation, and loading/error/empty states.

## Scenarios

### Claude full HooksConfigMenu component

#### opens and renders grouped hook rows

- Create menu and inspect default rows
   - Expected: closed.render() equals `Hooks config menu closed`
   - Expected: opened.state.isOpen is true
   - Expected: opened.rows().len() equals `4`
   - Expected: opened.groups().len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create menu and inspect default rows")
val hooks = sampleHookConfigs()
val closed = createHooksConfigMenu(hooks)
expect(closed.render()).to_equal("Hooks config menu closed")
val opened = closed.open()
expect(opened.state.isOpen).to_equal(true)
expect(opened.rows().len()).to_equal(4)
expect(opened.groups().len()).to_equal(4)
expect(opened.render()).to_contain("Hooks config 4/4")
expect(opened.render()).to_contain("> Run focused tests [Post tool use / Edit / User] enabled")
```

</details>

#### filters by event matcher mode and query

- Apply focused hook filters
   - Expected: filterHookConfigs(hooks, "focused", "PostToolUse", "Edit", "user").len() equals `1`
   - Expected: filterHookConfigs(hooks, "desktop", "Stop", "*", "local")[0].id equals `notify-stop`
   - Expected: model.rows().len() equals `1`
   - Expected: model.rows()[0].hook.id equals `submit-summary`
   - Expected: model.state.selectedIndex equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply focused hook filters")
val hooks = sampleHookConfigs()
expect(filterHookConfigs(hooks, "focused", "PostToolUse", "Edit", "user").len()).to_equal(1)
expect(filterHookConfigs(hooks, "desktop", "Stop", "*", "local")[0].id).to_equal("notify-stop")
val model = openHooksConfigMenu(hooks).eventFilter("submit").matcherFilter("prompt").modeFilter("project")
expect(model.rows().len()).to_equal(1)
expect(model.rows()[0].hook.id).to_equal("submit-summary")
expect(model.state.selectedIndex).to_equal(0)
```

</details>

#### moves selection and toggles enabled state

- Navigate rows and toggle selected hook
   - Expected: model.state.selectedIndex equals `1`
   - Expected: hook.id equals `pre-bash-format`
   - Expected: updated[0].enabled is false
   - Expected: toggled.state.lastAction equals `toggle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Navigate rows and toggle selected hook")
val hooks = sampleHookConfigs()
val model = openHooksConfigMenu(hooks).handleKey("down")
expect(model.state.selectedIndex).to_equal(1)
val selected = model.selectedHook()
if val hook = selected:
    expect(hook.id).to_equal("pre-bash-format")
val toggled = model.toggleSelected()
val updated = filterHookConfigs(toggled.hooks, "Format", "all", "all", "all")
expect(updated[0].enabled).to_equal(false)
expect(toggled.state.lastAction).to_equal("toggle")
```

</details>

#### edits prompt through dialog and validates hooks

- Open prompt dialog and save non-empty prompt
   - Expected: model.state.promptDialog.isOpen is true
   - Expected: failed.state.promptDialog.error equals `Prompt cannot be empty`
   - Expected: saved.state.promptDialog.isOpen is false
   - Expected: filterHookConfigs(saved.hooks, "one focused", "all", "all", "all").len() equals `1`
   - Expected: validateHookConfig(invalid) equals `Hook id is required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open prompt dialog and save non-empty prompt")
val hooks = sampleHookConfigs()
val model = openHooksConfigMenu(hooks).eventFilter("PostToolUse").openPromptForSelected()
expect(model.state.promptDialog.isOpen).to_equal(true)
expect(model.state.promptDialog.title).to_contain("Run focused tests")
val failed = model.updatePrompt(" ").applyPrompt()
expect(failed.state.promptDialog.error).to_equal("Prompt cannot be empty")
val saved = model.updatePrompt("Run one focused spec.").applyPrompt()
expect(saved.state.promptDialog.isOpen).to_equal(false)
expect(filterHookConfigs(saved.hooks, "one focused", "all", "all", "all").len()).to_equal(1)
val invalid = HookConfig.new("", "Broken", "PreToolUse", "Bash", "project", "", true, "project")
expect(validateHookConfig(invalid)).to_equal("Hook id is required")
```

</details>

#### renders loading error empty and summary states

- Check non-list states
   - Expected: openHooksConfigMenu(hooks).loading().render() equals `Loading hooks configuration...`
   - Expected: openHooksConfigMenu(hooks).fail("settings.json unreadable").render() equals `Hooks config error: settings.json unreadable`
   - Expected: openHooksConfigMenu([]).render() equals `No hooks configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check non-list states")
val hooks = sampleHookConfigs()
expect(openHooksConfigMenu(hooks).loading().render()).to_equal("Loading hooks configuration...")
expect(openHooksConfigMenu(hooks).fail("settings.json unreadable").render()).to_equal("Hooks config error: settings.json unreadable")
expect(openHooksConfigMenu([]).render()).to_equal("No hooks configured")
expect(openHooksConfigMenu(hooks).query("missing").render()).to_contain("No hooks match search \"missing\"")
expect(hooksConfigSummary(hooks, HooksConfigMenuState.closed().open())).to_contain("3 enabled")
```

</details>

#### exports source parity helpers

- Pin option helpers and modeled upstream names
   - Expected: hooksConfigModeledSourceFile() equals `src/components/hooks/HooksConfigMenu.tsx`
   - Expected: hooksConfigModeledStateHook() equals `useHooksConfigMenu`
   - Expected: hooksConfigModeledHookRowsHelper() equals `getHookRows`
   - Expected: hooksConfigModeledPromptDialog() equals `HookPromptDialog`
   - Expected: hooksConfigModeledLineCount() equals `577`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin option helpers and modeled upstream names")
val hooks = sampleHookConfigs()
expect(hookEventOptions()).to_contain("PreToolUse")
expect(hookModeOptions()).to_contain("local")
expect(hookMatcherOptions(hooks)).to_contain("Bash")
expect(hooksConfigModeledSourceFile()).to_equal("src/components/hooks/HooksConfigMenu.tsx")
expect(hooksConfigModeledStateHook()).to_equal("useHooksConfigMenu")
expect(hooksConfigModeledHookRowsHelper()).to_equal("getHookRows")
expect(hooksConfigModeledPromptDialog()).to_equal("HookPromptDialog")
expect(hooksConfigModeledLineCount()).to_equal(577)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
