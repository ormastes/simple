# Claude Full Hooks, IDE, and History Components

> Checks modern SSpec parity for history search, hook mode helpers, and IDE dialogs.

<!-- sdn-diagram:id=hooks_ide_history_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hooks_ide_history_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hooks_ide_history_spec -> std
hooks_ide_history_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hooks_ide_history_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Hooks, IDE, and History Components

Checks modern SSpec parity for history search, hook mode helpers, and IDE dialogs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/hooks_ide_history_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for history search, hook mode helpers, and IDE dialogs.

## Scenarios

### Claude full hooks IDE and history components

#### should render history and prompt dialog state

- Render history search
   - Expected: historySearchVisible(history) is true
   - Expected: historySearchNext(history, 2).selected_index equals `1`
- Render hook prompt dialog
   - Expected: hookPromptDialogCanSave(prompt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render history search")
val history = HistorySearchState.new(true, "deploy", 0, false, "")
expect(historySearchVisible(history)).to_equal(true)
expect(historySearchSummary(history)).to_contain("filtered")
expect(historySearchNext(history, 2).selected_index).to_equal(1)

step("Render hook prompt dialog")
val prompt = HookPromptDialogState.new(true, "Edit hook", "run tests", true)
expect(hookPromptDialogCanSave(prompt)).to_equal(true)
expect(hookPromptDialogSummary(prompt)).to_contain("dirty=true")
```

</details>

#### should render hook mode helpers

- Render event and hook mode labels
   - Expected: hookEventModeLabel("post") equals `After event`
   - Expected: hookEventModeCanRun("pre", true) is true
   - Expected: hookModeLabel("matcher") equals `Matcher hook`
   - Expected: hookModeRequiresPrompt("command") is true
- Render matcher and view state
   - Expected: matcherModeValid(matcher) is true
   - Expected: hookViewCanEdit(view) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render event and hook mode labels")
expect(hookEventModeLabel("post")).to_equal("After event")
expect(hookEventModeCanRun("pre", true)).to_equal(true)
expect(hookModeLabel("matcher")).to_equal("Matcher hook")
expect(hookModeRequiresPrompt("command")).to_equal(true)

step("Render matcher and view state")
val matcher = MatcherModeState.new("regex", ".*", true)
expect(matcherModeValid(matcher)).to_equal(true)
expect(matcherModeSummary(matcher)).to_contain("case")
val view = HookViewState.new("Format", "pre", "command", "glob", true)
expect(hookViewCanEdit(view)).to_equal(true)
expect(hookViewSummary(view)).to_contain("enabled")
```

</details>

#### should render IDE dialogs and status

- Render auto connect
   - Expected: ideAutoConnectCanConnect(autoState) is true
- Render onboarding and status
   - Expected: ideOnboardingCanContinue(onboarding) is true
   - Expected: ideOnboardingNext(onboarding).step equals `3`
   - Expected: ideStatusLabel(true, "VS Code") equals `VS Code connected`
   - Expected: ideStatusTone(false, true) equals `warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render auto connect")
val autoState = IdeAutoConnectState.new(true, "VS Code", true, false, "")
expect(ideAutoConnectCanConnect(autoState)).to_equal(true)
expect(ideAutoConnectSummary(autoState)).to_contain("ready")

step("Render onboarding and status")
val onboarding = IdeOnboardingState.new(true, 2, "VS Code", false)
expect(ideOnboardingCanContinue(onboarding)).to_equal(true)
expect(ideOnboardingNext(onboarding).step).to_equal(3)
expect(ideStatusLabel(true, "VS Code")).to_equal("VS Code connected")
expect(ideStatusTone(false, true)).to_equal("warning")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: historySearchDialogSourceLinesModeled() equals `117`
   - Expected: promptDialogSourceLinesModeled() equals `89`
   - Expected: selectEventModeSourceLinesModeled() equals `126`
   - Expected: selectHookModeSourceLinesModeled() equals `111`
   - Expected: selectMatcherModeSourceLinesModeled() equals `143`
   - Expected: viewHookModeSourceLinesModeled() equals `198`
   - Expected: ideAutoConnectDialogSourceLinesModeled() equals `153`
   - Expected: ideOnboardingDialogSourceLinesModeled() equals `166`
   - Expected: ideStatusIndicatorSourceLinesModeled() equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(historySearchDialogSourceLinesModeled()).to_equal(117)
expect(promptDialogSourceLinesModeled()).to_equal(89)
expect(selectEventModeSourceLinesModeled()).to_equal(126)
expect(selectHookModeSourceLinesModeled()).to_equal(111)
expect(selectMatcherModeSourceLinesModeled()).to_equal(143)
expect(viewHookModeSourceLinesModeled()).to_equal(198)
expect(ideAutoConnectDialogSourceLinesModeled()).to_equal(153)
expect(ideOnboardingDialogSourceLinesModeled()).to_equal(166)
expect(ideStatusIndicatorSourceLinesModeled()).to_equal(57)
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
