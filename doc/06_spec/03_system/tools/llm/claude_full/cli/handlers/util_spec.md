# Claude Full CLI Util Handlers

> Checks setup-token, doctor, and install subcommand behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Util Handlers

Checks setup-token, doctor, and install subcommand behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks setup-token, doctor, and install subcommand behavior.

## Scenarios

### Claude full cli util handlers

#### renders setup token flow

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders setup token flow
- Setup token logs, renders OAuth flow, and warns when auth is already external
   - Expected: warned.screen equals `setupTokenModeName()`
   - Expected: warned.warningShown is true
   - Expected: warned.message equals `setupTokenStartingMessage()`
   - Expected: quiet.warningShown is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders setup token flow")
step("Setup token logs, renders OAuth flow, and warns when auth is already external")
val warned = setupTokenHandler(false)
expect(warned.screen).to_equal(setupTokenModeName())
expect(warned.events).to_contain(setupTokenEventName())
expect(warned.warningShown).to_equal(true)
expect(warned.message).to_equal(setupTokenStartingMessage())
val quiet = setupTokenHandler(true)
expect(quiet.warningShown).to_equal(false)
```

</details>

#### renders doctor with plugins and MCP manager

- renders doctor with plugins and MCP manager
- Doctor logs and renders the plugin-aware wrapper
   - Expected: result.screen equals `doctor`
   - Expected: result.message equals `DoctorWithPlugins`
   - Expected: result.exitCode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders doctor with plugins and MCP manager")
step("Doctor logs and renders the plugin-aware wrapper")
val result = doctorHandler()
expect(result.screen).to_equal("doctor")
expect(result.events).to_contain(doctorEventName())
expect(result.message).to_equal("DoctorWithPlugins")
expect(result.exitCode).to_equal(0)
```

</details>

#### builds install command arguments and exit code

- builds install command arguments and exit code
- Target and force become args; failed output exits one
   - Expected: ok.setupCalled is true
   - Expected: ok.args equals `["stable", "--force"]`
   - Expected: ok.exitCode equals `0`
   - Expected: failed.args equals `[]`
   - Expected: failed.exitCode equals `1`
   - Expected: installArgs("nightly", false) equals `["nightly"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds install command arguments and exit code")
step("Target and force become args; failed output exits one")
val ok = installHandler("stable", true, "installed")
expect(ok.setupCalled).to_equal(true)
expect(ok.args).to_equal(["stable", "--force"])
expect(ok.exitCode).to_equal(0)
val failed = installHandler("", false, "failed to install")
expect(failed.args).to_equal([])
expect(failed.exitCode).to_equal(1)
expect(installArgs("nightly", false)).to_equal(["nightly"])
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin helper flags from the TS handler
   - Expected: installSetupModeName() equals `default`
   - Expected: doctorUsesPluginManager() is true
   - Expected: doctorUsesSuspenseFallbackNull() is true
   - Expected: doctorUsesMcpConnectionManager() is true
   - Expected: doctorStrictMcpConfig() is false
   - Expected: setupTokenUsesAppStateOnChange() is true
   - Expected: setupTokenUsesKeybindingSetup() is true
   - Expected: setupTokenRendersWelcome() is true
   - Expected: installCallsSetupBeforeCommand() is true
   - Expected: installFailureExitCode() equals `1`
   - Expected: installSuccessExitCode() equals `0`
   - Expected: cliSubcommandsIntentionallyExit() is true
   - Expected: utilHandlerSourceLinesModeled() equals `109`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin helper flags from the TS handler")
expect(setupTokenWarningText()).to_contain("Warning:")
expect(installSetupModeName()).to_equal("default")
expect(doctorUsesPluginManager()).to_equal(true)
expect(doctorUsesSuspenseFallbackNull()).to_equal(true)
expect(doctorUsesMcpConnectionManager()).to_equal(true)
expect(doctorStrictMcpConfig()).to_equal(false)
expect(setupTokenUsesAppStateOnChange()).to_equal(true)
expect(setupTokenUsesKeybindingSetup()).to_equal(true)
expect(setupTokenRendersWelcome()).to_equal(true)
expect(installCallsSetupBeforeCommand()).to_equal(true)
expect(installFailureExitCode()).to_equal(1)
expect(installSuccessExitCode()).to_equal(0)
expect(cliSubcommandsIntentionallyExit()).to_equal(true)
expect(utilHandlerSourceLinesModeled()).to_equal(109)
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

- Canonical SPipe generation for source `e047402d879abaffed80baec0ec9b7b8e672b8a8666dad32b987661935d2cb14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e047402d879abaffed80baec0ec9b7b8e672b8a8666dad32b987661935d2cb14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e047402d879abaffed80baec0ec9b7b8e672b8a8666dad32b987661935d2cb14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/util_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/util_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/util_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders setup token flow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders doctor with plugins and MCP manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds install command arguments and exit code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
