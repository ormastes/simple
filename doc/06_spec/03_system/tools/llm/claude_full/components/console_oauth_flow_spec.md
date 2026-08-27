# Claude Full Console OAuth Flow

> ConsoleOAuthFlow models the terminal sign-in state used by Claude Full when a provider asks the user to open a browser URL and enter or copy a one-time code. The executable spec covers provider defaults, auth URL and code normalization, step labels, terminal status copy, success/error behavior, copy/open actions, and the source helper used for parity accounting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Console OAuth Flow

ConsoleOAuthFlow models the terminal sign-in state used by Claude Full when a provider asks the user to open a browser URL and enter or copy a one-time code. The executable spec covers provider defaults, auth URL and code normalization, step labels, terminal status copy, success/error behavior, copy/open actions, and the source helper used for parity accounting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

ConsoleOAuthFlow models the terminal sign-in state used by Claude Full when a
provider asks the user to open a browser URL and enter or copy a one-time code.
The executable spec covers provider defaults, auth URL and code normalization,
step labels, terminal status copy, success/error behavior, copy/open actions,
and the source helper used for parity accounting.

## Examples

Create the default Anthropic provider, build a waiting state with a browser URL
and code, render the instruction text, then use the copy/open helpers to expose
side-effect requests without performing the side effects inside the model.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Scenarios

### Claude full console oauth flow

#### should model provider defaults and source helper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model provider defaults and source helper
- Create provider
   - Expected: provider.id equals `anthropic`
   - Expected: provider.name equals `Anthropic`
   - Expected: provider.authUrl equals `https://example.test/auth`
   - Expected: provider.codeLabel equals `code`
   - Expected: consoleOAuthSourceHelper(provider) equals `ConsoleOAuthFlow:anthropic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model provider defaults and source helper")
step("Create provider")
val provider = ConsoleOAuthProvider.new("", "", " https://example.test/auth ", "", "")
expect(provider.id).to_equal("anthropic")
expect(provider.name).to_equal("Anthropic")
expect(provider.authUrl).to_equal("https://example.test/auth")
expect(provider.codeLabel).to_equal("code")
expect(consoleOAuthSourceHelper(provider)).to_equal("ConsoleOAuthFlow:anthropic")
```

</details>

#### should model url code state and actions

- should model url code state and actions
- Create waiting flow
   - Expected: state.status equals `waiting`
   - Expected: state.authUrl equals `https://console.anthropic.com/oauth/authorize`
   - Expected: state.userCode equals `ABCD-EFGH`
   - Expected: consoleOAuthCopyAction(state) equals `copy-code:ABCD-EFGH`
   - Expected: consoleOAuthCanCopy(state) is true
   - Expected: consoleOAuthCanOpen(state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model url code state and actions")
step("Create waiting flow")
val provider = consoleOAuthAnthropicProvider()
val state = ConsoleOAuthFlowState.new(provider, "waiting", "", " ABCD-EFGH ", false, false, "")
expect(state.status).to_equal("waiting")
expect(state.authUrl).to_equal("https://console.anthropic.com/oauth/authorize")
expect(state.userCode).to_equal("ABCD-EFGH")
expect(consoleOAuthInstruction(state)).to_contain("ABCD-EFGH")
expect(consoleOAuthCopyAction(state)).to_equal("copy-code:ABCD-EFGH")
expect(consoleOAuthOpenAction(state)).to_contain("open-url:https://")
expect(consoleOAuthCanCopy(state)).to_equal(true)
expect(consoleOAuthCanOpen(state)).to_equal(true)
```

</details>

#### should model step labels and success error statuses

- should model step labels and success error statuses
- Read labels
   - Expected: consoleOAuthStepLabel("idle") equals `Ready to sign in`
   - Expected: consoleOAuthStepLabel("opening-browser") equals `Opening browser`
   - Expected: consoleOAuthStepLabel("copied-code") equals `Code copied`
   - Expected: consoleOAuthStatusLine(success) equals `Anthropic authentication complete`
   - Expected: consoleOAuthPrimaryAction("success") equals `continue`
   - Expected: consoleOAuthPrimaryAction("error") equals `retry`
   - Expected: consoleOAuthNormalizeStatus("bogus") equals `idle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model step labels and success error statuses")
step("Read labels")
val provider = consoleOAuthAnthropicProvider()
val success = ConsoleOAuthFlowState.new(provider, "success", "", "DONE", true, true, "")
val failure = ConsoleOAuthFlowState.new(provider, "error", "", "", false, false, "access denied")
expect(consoleOAuthStepLabel("idle")).to_equal("Ready to sign in")
expect(consoleOAuthStepLabel("opening-browser")).to_equal("Opening browser")
expect(consoleOAuthStepLabel("copied-code")).to_equal("Code copied")
expect(consoleOAuthStatusLine(success)).to_equal("Anthropic authentication complete")
expect(consoleOAuthStatusLine(failure)).to_contain("access denied")
expect(consoleOAuthPrimaryAction("success")).to_equal("continue")
expect(consoleOAuthPrimaryAction("error")).to_equal("retry")
expect(consoleOAuthNormalizeStatus("bogus")).to_equal("idle")
```

</details>

#### should model copy open mutations and source floor

- should model copy open mutations and source floor
- Apply actions
   - Expected: state.copyCode().copied is true
   - Expected: state.openUrl().opened is true
   - Expected: state.withStatus("success", "ignored").status equals `success`
   - Expected: consoleOAuthSourceLinesModeled() equals `630`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model copy open mutations and source floor")
step("Apply actions")
val provider = consoleOAuthAnthropicProvider()
val state = ConsoleOAuthFlowState.new(provider, "waiting", "https://auth.test", "CODE", false, false, "")
expect(state.copyCode().copied).to_equal(true)
expect(state.openUrl().opened).to_equal(true)
expect(state.withStatus("success", "ignored").status).to_equal("success")
expect(consoleOAuthRenderSummary(state)).to_contain("Sign in with Anthropic")
expect(consoleOAuthSourceLinesModeled()).to_equal(630)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee67a4281078bfe15ada80b5f9ad2cac73aa1e97bdfb6c9b5c67ebbffcf2da0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee67a4281078bfe15ada80b5f9ad2cac73aa1e97bdfb6c9b5c67ebbffcf2da0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee67a4281078bfe15ada80b5f9ad2cac73aa1e97bdfb6c9b5c67ebbffcf2da0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model provider defaults and source helper' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model provider defaults and source helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model url code state and actions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model url code state and actions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model step labels and success error statuses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model step labels and success error statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model copy open mutations and source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
