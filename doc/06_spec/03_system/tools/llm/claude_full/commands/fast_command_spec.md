# Claude Full Fast Command

> Mirrors `tmp/claude/claude-code-main/src/commands/fast` command metadata,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Fast Command

Mirrors `tmp/claude/claude-code-main/src/commands/fast` command metadata,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/fast` command metadata,
feature gating, picker text, shortcut state updates, unavailable handling, and
analytics labels for the FAST-only Claude-full parity slice.

## Scenarios

### Claude full fast command

#### matches command metadata and feature gating

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches command metadata and feature gating
   - Expected: enabled.typeName equals `local-jsx`
   - Expected: enabled.name equals `fast`
   - Expected: enabled.description equals `Toggle fast mode (Opus 4.6 only)`
   - Expected: enabled.availability equals `["claude-ai", "console"]`
   - Expected: enabled.enabled is true
   - Expected: enabled.hidden is false
   - Expected: enabled.argumentHint equals `[on|off]`
   - Expected: enabled.immediate is true
   - Expected: enabled.loadPath equals `./fast.js`
   - Expected: disabled.enabled is false
   - Expected: disabled.hidden is true
   - Expected: disabled.immediate is false
   - Expected: fastIndexSourceLinesModeled() equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches command metadata and feature gating")
val enabled = fastCommand(true, true)
expect(enabled.typeName).to_equal("local-jsx")
expect(enabled.name).to_equal("fast")
expect(enabled.description).to_equal("Toggle fast mode (Opus 4.6 only)")
expect(enabled.availability).to_equal(["claude-ai", "console"])
expect(enabled.enabled).to_equal(true)
expect(enabled.hidden).to_equal(false)
expect(enabled.argumentHint).to_equal("[on|off]")
expect(enabled.immediate).to_equal(true)
expect(enabled.loadPath).to_equal("./fast.js")

val disabled = fastCommand(false, false)
expect(disabled.enabled).to_equal(false)
expect(disabled.hidden).to_equal(true)
expect(disabled.immediate).to_equal(false)
expect(fastIndexSourceLinesModeled()).to_equal(26)
```

</details>

#### applies fast mode and switches unsupported models

- applies fast mode and switches unsupported models
   - Expected: enabled.appState.fastMode is true
   - Expected: enabled.appState.mainLoopModel equals `opus`
   - Expected: enabled.appState.mainLoopModelForSession equals ``
   - Expected: enabled.settingsFastMode equals `true`
   - Expected: enabled.cooldownCleared is true
   - Expected: enabled.modelSwitched is true
   - Expected: kept.appState.mainLoopModel equals `claude-opus-4-6`
   - Expected: kept.appState.mainLoopModelForSession equals `claude-opus-4-6`
   - Expected: kept.modelSwitched is false
   - Expected: off.appState.fastMode is false
   - Expected: off.appState.mainLoopModel equals `claude-opus-4-6`
   - Expected: off.settingsFastMode equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies fast mode and switches unsupported models")
val sonnet = FastAppState.new("claude-sonnet-4-5", "claude-sonnet-4-5", false)
val enabled = applyFastMode(true, sonnet, true, false)
expect(enabled.appState.fastMode).to_equal(true)
expect(enabled.appState.mainLoopModel).to_equal("opus")
expect(enabled.appState.mainLoopModelForSession).to_equal("")
expect(enabled.settingsFastMode).to_equal("true")
expect(enabled.cooldownCleared).to_equal(true)
expect(enabled.modelSwitched).to_equal(true)

val opus = FastAppState.new("claude-opus-4-6", "claude-opus-4-6", false)
val kept = applyFastMode(true, opus, true, true)
expect(kept.appState.mainLoopModel).to_equal("claude-opus-4-6")
expect(kept.appState.mainLoopModelForSession).to_equal("claude-opus-4-6")
expect(kept.modelSwitched).to_equal(false)

val off = applyFastMode(false, kept.appState, true, false)
expect(off.appState.fastMode).to_equal(false)
expect(off.appState.mainLoopModel).to_equal("claude-opus-4-6")
expect(off.settingsFastMode).to_equal("")
```

</details>

#### routes shortcut calls and unavailable responses

- routes shortcut calls and unavailable responses
   - Expected: disabled.rendered equals `none`
   - Expected: disabled.doneMessage equals ``
   - Expected: disabled.prefetchAwaited is false
   - Expected: enabledCall.rendered equals `none`
   - Expected: enabledCall.doneMessage equals `⚡ Fast mode ON · model set to Opus 4.6 · $30/$150 per Mtok`
   - Expected: enabledCall.eventName equals `tengu_fast_mode_toggled`
   - Expected: enabledCall.eventSource equals `shortcut`
   - Expected: enabledCall.appState.fastMode is true
   - Expected: enabledCall.modelSwitched is true
   - Expected: enabledCall.prefetchAwaited is true
   - Expected: disabledCall.doneMessage equals `Fast mode OFF`
   - Expected: disabledCall.appState.fastMode is false
   - Expected: disabledCall.settingsFastMode equals ``
   - Expected: unavailable.doneMessage equals `Fast mode unavailable: Fast mode requires a paid subscription`
   - Expected: unavailable.eventName equals ``
   - Expected: unavailable.appState.fastMode is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes shortcut calls and unavailable responses")
val state = FastAppState.new("claude-sonnet-4-5", "claude-sonnet-4-5", false)
val disabled = callFast("on", state, false, "", false)
expect(disabled.rendered).to_equal("none")
expect(disabled.doneMessage).to_equal("")
expect(disabled.prefetchAwaited).to_equal(false)

val enabledCall = callFast(" ON ", state, true, "", false)
expect(enabledCall.rendered).to_equal("none")
expect(enabledCall.doneMessage).to_equal("⚡ Fast mode ON · model set to Opus 4.6 · $30/$150 per Mtok")
expect(enabledCall.eventName).to_equal("tengu_fast_mode_toggled")
expect(enabledCall.eventSource).to_equal("shortcut")
expect(enabledCall.appState.fastMode).to_equal(true)
expect(enabledCall.modelSwitched).to_equal(true)
expect(enabledCall.prefetchAwaited).to_equal(true)

val disabledCall = callFast("off", enabledCall.appState, true, "", false)
expect(disabledCall.doneMessage).to_equal("Fast mode OFF")
expect(disabledCall.appState.fastMode).to_equal(false)
expect(disabledCall.settingsFastMode).to_equal("")

val unavailable = callFast("on", state, true, "Fast mode requires a paid subscription", false)
expect(unavailable.doneMessage).to_equal("Fast mode unavailable: Fast mode requires a paid subscription")
expect(unavailable.eventName).to_equal("")
expect(unavailable.appState.fastMode).to_equal(false)
```

</details>

#### shows picker for non-shortcut args and renders visible content

- shows picker for non-shortcut args and renders visible content
   - Expected: pickerCall.rendered equals `picker`
   - Expected: pickerCall.eventName equals `tengu_fast_mode_picker_shown`
   - Expected: pickerCall.unavailableReason equals ``
   - Expected: picker.title equals `⚡ Fast mode (research preview)`
   - Expected: picker.subtitle equals `High-speed mode for Opus 4.6. Billed as extra usage at a premium rate. Separa... (full value in folded executable source)`
   - Expected: picker.inputGuide equals `Tab to toggle · Enter to confirm · Esc to cancel`
   - Expected: picker.link equals `https://code.claude.com/docs/en/fast-mode`
   - Expected: picker.color equals `fastMode`
   - Expected: unavailableView.inputGuide equals `Esc to cancel`
   - Expected: unavailableView.body equals `Fast mode is not available`
   - Expected: renderFastModePicker(false, "", "", "", true, "q").inputGuide equals `Press q again to exit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows picker for non-shortcut args and renders visible content")
val state = FastAppState.new("claude-opus-4-6", "", true)
val pickerCall = callFast("", state, true, "", false)
expect(pickerCall.rendered).to_equal("picker")
expect(pickerCall.eventName).to_equal("tengu_fast_mode_picker_shown")
expect(pickerCall.unavailableReason).to_equal("")

val picker = renderFastModePicker(true, "", "overloaded", "2m", false, "Esc")
expect(picker.title).to_equal("⚡ Fast mode (research preview)")
expect(picker.subtitle).to_equal("High-speed mode for Opus 4.6. Billed as extra usage at a premium rate. Separate rate limits apply.")
expect(picker.inputGuide).to_equal("Tab to toggle · Enter to confirm · Esc to cancel")
expect(picker.body).to_contain("Fast mode ON  $30/$150 per Mtok")
expect(picker.body).to_contain("Fast mode overloaded and is temporarily unavailable · resets in 2m")
expect(picker.link).to_equal("https://code.claude.com/docs/en/fast-mode")
expect(picker.color).to_equal("fastMode")

val unavailableView = renderFastModePicker(false, "Fast mode is not available", "", "", false, "Esc")
expect(unavailableView.inputGuide).to_equal("Esc to cancel")
expect(unavailableView.body).to_equal("Fast mode is not available")
expect(renderFastModePicker(false, "", "", "", true, "q").inputGuide).to_equal("Press q again to exit")
```

</details>

#### confirms, cancels, and toggles picker decisions

- confirms, cancels, and toggles picker decisions
   - Expected: confirm.doneMessage equals `⚡ Fast mode ON · model set to Opus 4.6 · $30/$150 per Mtok`
   - Expected: confirm.eventSource equals `picker`
   - Expected: confirm.appState.mainLoopModel equals `opus[1m]`
   - Expected: confirm.appState.mainLoopModelForSession equals ``
   - Expected: blockedConfirm.doneMessage equals ``
   - Expected: blockedConfirm.appState.fastMode is false
   - Expected: keptOn.doneMessage equals `⚡ Kept Fast mode ON`
   - Expected: keptOn.display equals `system`
   - Expected: forcedOff.doneMessage equals `Fast mode OFF`
   - Expected: forcedOff.display equals `system`
   - Expected: forcedOff.appState.fastMode is false
   - Expected: forcedOff.settingsFastMode equals ``
   - Expected: togglePickerSelection(false, "") is true
   - Expected: togglePickerSelection(false, "Fast mode disabled") is false
   - Expected: isFastModeSupportedByModel(true, "CLAUDE-OPUS-4-6") is true
   - Expected: isFastModeSupportedByModel(false, "claude-opus-4-6") is false
   - Expected: fastSourceLinesModeled() equals `268`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("confirms, cancels, and toggles picker decisions")
val state = FastAppState.new("claude-sonnet-4-5", "claude-sonnet-4-5", false)
val confirm = confirmFastModePicker(true, state, true, "", true)
expect(confirm.doneMessage).to_equal("⚡ Fast mode ON · model set to Opus 4.6 · $30/$150 per Mtok")
expect(confirm.eventSource).to_equal("picker")
expect(confirm.appState.mainLoopModel).to_equal("opus[1m]")
expect(confirm.appState.mainLoopModelForSession).to_equal("")

val blockedConfirm = confirmFastModePicker(true, state, true, "Fast mode has been disabled by your organization", false)
expect(blockedConfirm.doneMessage).to_equal("")
expect(blockedConfirm.appState.fastMode).to_equal(false)

val keptOn = cancelFastModePicker(true, FastAppState.new("claude-opus-4-6", "", true), true, "", false)
expect(keptOn.doneMessage).to_equal("⚡ Kept Fast mode ON")
expect(keptOn.display).to_equal("system")

val forcedOff = cancelFastModePicker(true, FastAppState.new("claude-opus-4-6", "", true), true, "Fast mode is currently unavailable", false)
expect(forcedOff.doneMessage).to_equal("Fast mode OFF")
expect(forcedOff.display).to_equal("system")
expect(forcedOff.appState.fastMode).to_equal(false)
expect(forcedOff.settingsFastMode).to_equal("")

expect(togglePickerSelection(false, "")).to_equal(true)
expect(togglePickerSelection(false, "Fast mode disabled")).to_equal(false)
expect(isFastModeSupportedByModel(true, "CLAUDE-OPUS-4-6")).to_equal(true)
expect(isFastModeSupportedByModel(false, "claude-opus-4-6")).to_equal(false)
expect(fastSourceLinesModeled()).to_equal(268)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92160c318b5f7494ff82bd981055191d732195791c0739a423979843a1661017`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92160c318b5f7494ff82bd981055191d732195791c0739a423979843a1661017`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92160c318b5f7494ff82bd981055191d732195791c0739a423979843a1661017`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/fast_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/fast_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/fast_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches command metadata and feature gating' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies fast mode and switches unsupported models' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/fast_command_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes shortcut calls and unavailable responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
