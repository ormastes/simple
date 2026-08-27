# Claude Full HooksConfigMenu Component

> Checks hook rows, enable-disable state, filters, prompt dialogs, summaries, validation, and loading/error/empty states.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks hook rows, enable-disable state, filters, prompt dialogs, summaries, validation, and loading/error/empty states.

## Scenarios

### Claude full HooksConfigMenu component

#### opens and renders grouped hook rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens and renders grouped hook rows
- Create menu and inspect default rows
   - Expected: closed.render() equals `Hooks config menu closed`
   - Expected: opened.state.isOpen is true
   - Expected: opened.rows().len() equals `4`
   - Expected: opened.groups().len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("opens and renders grouped hook rows")
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

- filters by event matcher mode and query
- Apply focused hook filters
   - Expected: filterHookConfigs(hooks, "focused", "PostToolUse", "Edit", "user").len() equals `1`
   - Expected: filterHookConfigs(hooks, "desktop", "Stop", "*", "local")[0].id equals `notify-stop`
   - Expected: model.rows().len() equals `1`
   - Expected: model.rows()[0].hook.id equals `submit-summary`
   - Expected: model.state.selectedIndex equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters by event matcher mode and query")
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

- moves selection and toggles enabled state
- Navigate rows and toggle selected hook
   - Expected: model.state.selectedIndex equals `1`
   - Expected: hook.id equals `pre-bash-format`
   - Expected: updated[0].enabled is false
   - Expected: toggled.state.lastAction equals `toggle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("moves selection and toggles enabled state")
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

- edits prompt through dialog and validates hooks
- Open prompt dialog and save non-empty prompt
   - Expected: model.state.promptDialog.isOpen is true
   - Expected: failed.state.promptDialog.error equals `Prompt cannot be empty`
   - Expected: saved.state.promptDialog.isOpen is false
   - Expected: filterHookConfigs(saved.hooks, "one focused", "all", "all", "all").len() equals `1`
   - Expected: validateHookConfig(invalid) equals `Hook id is required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edits prompt through dialog and validates hooks")
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

- renders loading error empty and summary states
- Check non-list states
   - Expected: openHooksConfigMenu(hooks).loading().render() equals `Loading hooks configuration...`
   - Expected: openHooksConfigMenu(hooks).fail("settings.json unreadable").render() equals `Hooks config error: settings.json unreadable`
   - Expected: openHooksConfigMenu([]).render() equals `No hooks configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders loading error empty and summary states")
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

- exports source parity helpers
- Pin option helpers and modeled upstream names
   - Expected: hooksConfigModeledSourceFile() equals `src/components/hooks/HooksConfigMenu.tsx`
   - Expected: hooksConfigModeledStateHook() equals `useHooksConfigMenu`
   - Expected: hooksConfigModeledHookRowsHelper() equals `getHookRows`
   - Expected: hooksConfigModeledPromptDialog() equals `HookPromptDialog`
   - Expected: hooksConfigModeledLineCount() equals `577`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source parity helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f0de11f7b7ed93dfd57b20be8ee90bf1b5da354eff9f6425f21ac885b48c060`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f0de11f7b7ed93dfd57b20be8ee90bf1b5da354eff9f6425f21ac885b48c060`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f0de11f7b7ed93dfd57b20be8ee90bf1b5da354eff9f6425f21ac885b48c060`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens and renders grouped hook rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by event matcher mode and query' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/hooks_config_menu_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves selection and toggles enabled state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
