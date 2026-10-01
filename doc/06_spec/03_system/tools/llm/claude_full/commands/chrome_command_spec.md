# Claude Full Chrome Command

> Mirrors `tmp/claude/claude-code-main/src/commands/chrome` command metadata,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Chrome Command

Mirrors `tmp/claude/claude-code-main/src/commands/chrome` command metadata,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/chrome` command metadata,
menu option construction, disabled states, and action effects.

## Scenarios

### Claude full chrome command

#### matches command metadata and non-interactive gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches command metadata and non-interactive gate
- Load command metadata for an interactive session
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `chrome`
   - Expected: command.description equals `Claude in Chrome (Beta) settings`
   - Expected: command.availability.len() equals `1`
   - Expected: command.availability[0] equals `claude-ai`
   - Expected: command.loadPath equals `./chrome.js`
   - Expected: command.enabled is true
- Disable the command in non-interactive sessions
   - Expected: disabled.enabled is false
   - Expected: chromeIndexSourceLinesModeled() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches command metadata and non-interactive gate")
step("Load command metadata for an interactive session")
val command = chromeCommand(false)

expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("chrome")
expect(command.description).to_equal("Claude in Chrome (Beta) settings")
expect(command.availability.len()).to_equal(1)
expect(command.availability[0]).to_equal("claude-ai")
expect(command.loadPath).to_equal("./chrome.js")
expect(command.enabled).to_equal(true)

step("Disable the command in non-interactive sessions")
val disabled = chromeCommand(true)
expect(disabled.enabled).to_equal(false)
expect(chromeIndexSourceLinesModeled()).to_equal(13)
```

</details>

#### builds chrome dialog copy and menu options

- builds chrome dialog copy and menu options
- Expose the same dialog strings and URLs as the upstream menu
   - Expected: chromeDialogTitle() equals `Claude in Chrome (Beta)`
   - Expected: chromeDialogColor() equals `chromeYellow`
   - Expected: chromeExtensionUrl() equals `https://claude.ai/chrome`
   - Expected: chromePermissionsUrl() equals `https://clau.de/chrome/permissions`
   - Expected: chromeReconnectUrl() equals `https://clau.de/chrome/reconnect`
   - Expected: chromeLearnMoreUrl() equals `https://code.claude.com/docs/en/chrome`
   - Expected: chromeUsageText() equals `claude --chrome or claude --no-chrome`
- Include install first only when extension is missing outside homespace
   - Expected: missing.len() equals `4`
   - Expected: missing[0].label equals `Install Chrome extension`
   - Expected: missing[0].value equals `install-extension`
   - Expected: missing[1].label equals `Manage permissions (requires extension)`
   - Expected: missing[2].label equals `Reconnect extension (requires extension)`
   - Expected: missing[3].label equals `Enabled by default: No`
- Skip install once the extension is present and show enabled default
   - Expected: installed.len() equals `3`
   - Expected: installed[0].label equals `Manage permissions`
   - Expected: installed[1].label equals `Reconnect extension`
   - Expected: installed[2].label equals `Enabled by default: Yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds chrome dialog copy and menu options")
step("Expose the same dialog strings and URLs as the upstream menu")
expect(chromeDialogTitle()).to_equal("Claude in Chrome (Beta)")
expect(chromeDialogColor()).to_equal("chromeYellow")
expect(chromeExtensionUrl()).to_equal("https://claude.ai/chrome")
expect(chromePermissionsUrl()).to_equal("https://clau.de/chrome/permissions")
expect(chromeReconnectUrl()).to_equal("https://clau.de/chrome/reconnect")
expect(chromeLearnMoreUrl()).to_equal("https://code.claude.com/docs/en/chrome")
expect(chromeUsageText()).to_equal("claude --chrome or claude --no-chrome")
expect(chromeIntroText()).to_contain("capture screenshots")
expect(chromePermissionsHelpText()).to_contain("Site-level permissions")
expect(chromeWslErrorText()).to_contain("not supported in WSL")
expect(chromeSubscriberErrorText()).to_contain("requires a claude.ai subscription")

step("Include install first only when extension is missing outside homespace")
val missing = chromeOptions(false, false, false)
expect(missing.len()).to_equal(4)
expect(missing[0].label).to_equal("Install Chrome extension")
expect(missing[0].value).to_equal("install-extension")
expect(missing[1].label).to_equal("Manage permissions (requires extension)")
expect(missing[2].label).to_equal("Reconnect extension (requires extension)")
expect(missing[3].label).to_equal("Enabled by default: No")

step("Skip install once the extension is present and show enabled default")
val installed = chromeOptions(true, false, true)
expect(installed.len()).to_equal(3)
expect(installed[0].label).to_equal("Manage permissions")
expect(installed[1].label).to_equal("Reconnect extension")
expect(installed[2].label).to_equal("Enabled by default: Yes")
```

</details>

#### mirrors status, disabled, and action state transitions

- mirrors status, disabled, and action state transitions
- Evaluate status labels and disabled rules
   - Expected: chromeIsConnected("claude-in-chrome", "connected") is true
   - Expected: chromeIsConnected("other", "connected") is false
   - Expected: chromeStatusText(true) equals `Enabled`
   - Expected: chromeStatusText(false) equals `Disabled`
   - Expected: chromeExtensionStatusText(true) equals `Installed`
   - Expected: chromeExtensionStatusText(false) equals `Not detected`
   - Expected: chromeRequiresExtensionSuffix(false) equals ` (requires extension)`
   - Expected: chromeDefaultLabel(true) equals `Enabled by default: Yes`
   - Expected: chromeIsDisabled(true, true) is true
   - Expected: chromeIsDisabled(false, false) is true
   - Expected: chromeIsDisabled(false, true) is false
- Apply install, reconnect, permissions, and toggle actions
   - Expected: install.showInstallHint is true
   - Expected: install.selectKey equals `1`
   - Expected: install.openedUrl equals `https://claude.ai/chrome`
   - Expected: install.openMode equals `chrome`
   - Expected: reconnect.isExtensionInstalled is true
   - Expected: reconnect.showInstallHint is false
   - Expected: reconnect.openedUrl equals `https://clau.de/chrome/reconnect`
   - Expected: permissions.openedUrl equals `https://clau.de/chrome/permissions`
   - Expected: permissions.openMode equals `browser`
   - Expected: toggled.enabledByDefault is true
   - Expected: toggled.selectKey equals `permissions.selectKey`
   - Expected: chromeCallSnapshot(true, true, true, false).enabledByDefault is true
   - Expected: chromeSourceLinesModeled() equals `284`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mirrors status, disabled, and action state transitions")
step("Evaluate status labels and disabled rules")
expect(chromeIsConnected("claude-in-chrome", "connected")).to_equal(true)
expect(chromeIsConnected("other", "connected")).to_equal(false)
expect(chromeStatusText(true)).to_equal("Enabled")
expect(chromeStatusText(false)).to_equal("Disabled")
expect(chromeExtensionStatusText(true)).to_equal("Installed")
expect(chromeExtensionStatusText(false)).to_equal("Not detected")
expect(chromeRequiresExtensionSuffix(false)).to_equal(" (requires extension)")
expect(chromeDefaultLabel(true)).to_equal("Enabled by default: Yes")
expect(chromeIsDisabled(true, true)).to_equal(true)
expect(chromeIsDisabled(false, false)).to_equal(true)
expect(chromeIsDisabled(false, true)).to_equal(false)

step("Apply install, reconnect, permissions, and toggle actions")
val initial = ChromeMenuState.new(false, false)
val install = chromeHandleAction("install-extension", initial, false, false)
expect(install.showInstallHint).to_equal(true)
expect(install.selectKey).to_equal(1)
expect(install.openedUrl).to_equal("https://claude.ai/chrome")
expect(install.openMode).to_equal("chrome")

val reconnect = chromeHandleAction("reconnect", install, false, true)
expect(reconnect.isExtensionInstalled).to_equal(true)
expect(reconnect.showInstallHint).to_equal(false)
expect(reconnect.openedUrl).to_equal("https://clau.de/chrome/reconnect")

val permissions = chromeHandleAction("manage-permissions", reconnect, true, true)
expect(permissions.openedUrl).to_equal("https://clau.de/chrome/permissions")
expect(permissions.openMode).to_equal("browser")

val toggled = chromeHandleAction("toggle-default", permissions, false, true)
expect(toggled.enabledByDefault).to_equal(true)
expect(toggled.selectKey).to_equal(permissions.selectKey)
expect(chromeCallSnapshot(true, true, true, false).enabledByDefault).to_equal(true)
expect(chromeSourceLinesModeled()).to_equal(284)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `576d64503122989514cb7dfa7cafbd2cb82d8179a54b1ecc1c4a573586125529`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `576d64503122989514cb7dfa7cafbd2cb82d8179a54b1ecc1c4a573586125529`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `576d64503122989514cb7dfa7cafbd2cb82d8179a54b1ecc1c4a573586125529`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/chrome_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/chrome_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/chrome_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches command metadata and non-interactive gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds chrome dialog copy and menu options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/chrome_command_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mirrors status, disabled, and action state transitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
