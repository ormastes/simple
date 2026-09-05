# Claude Full Install Command

> Purpose: should expose install command metadata and source size

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install Command

Purpose: should expose install command metadata and source size

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should expose install command metadata and source size
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Install Command

Checks modern SSpec parity for commands/install.tsx.

## Scenarios

### Claude full install command

#### should expose install command metadata and source size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose install command metadata and source size
- Verify: should expose install command metadata and source size
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `install`
   - Expected: command.description equals `Install Claude Code native build`
   - Expected: command.argumentHint equals `[options]`
   - Expected: installSourceLinesModeled() equals `299`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose install command metadata and source size")
step("Verify: should expose install command metadata and source size")
# @req: REQ-TOOLS-InstComm-001
val command = installCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("install")
expect(command.description).to_equal("Install Claude Code native build")
expect(command.argumentHint).to_equal("[options]")
expect(installSourceLinesModeled()).to_equal(299)  # oracle: value fixed by the spec contract
```

</details>

#### should parse force and first non-flag target

- should parse force and first non-flag target
- Verify: should parse force and first non-flag target
   - Expected: parsed.force is true
   - Expected: parsed.target equals `stable`
   - Expected: defaults.force is false
   - Expected: defaults.target equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse force and first non-flag target")
step("Verify: should parse force and first non-flag target")
# @req: REQ-TOOLS-InstComm-001
val parsed = parseInstallArgs(["--force", "--verbose", "stable", "1.0.34"])
expect(parsed.force).to_equal(true)
expect(parsed.target).to_equal("stable")
val defaults = parseInstallArgs(["--dry-run"])
expect(defaults.force).to_equal(false)
expect(defaults.target).to_equal("")
```

</details>

#### should model install paths and setup notes

- should model install paths and setup notes
- Verify: should model install paths and setup notes
   - Expected: getInstallationPath("linux", "/home/me") equals `~/.local/bin/claude`
   - Expected: setupNotes([]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model install paths and setup notes")
step("Verify: should model install paths and setup notes")
# @req: REQ-TOOLS-InstComm-001
expect(getInstallationPath("linux", "/home/me")).to_equal("~/.local/bin/claude")
expect(getInstallationPath("win32", "C:/Users/me")).to_contain("claude.exe")
expect(setupNotes([])).to_equal("")
val notes = setupNotes(["Add ~/.local/bin to PATH", "Restart shell"])
expect(notes).to_contain("Setup notes:")
expect(notes).to_contain("Restart shell")
```

</details>

#### should run success flow with setup and warning messages

- should run success flow with setup and warning messages
- Verify: should run success flow with setup and warning messages
   - Expected: result.finalState equals `success`
   - Expected: result.version equals `1.0.34`
   - Expected: result.channelOrVersion equals `stable`
   - Expected: result.savedChannel equals `stable`
   - Expected: result.analyticsEvent equals `tengu_claude_install_command`
   - Expected: result.hasVersion equals `1`
   - Expected: result.forced equals `1`
   - Expected: result.cleanupAttempted is true
   - Expected: result.shellAliasCleanupAttempted is true
   - Expected: result.checkInstallCalled is true
   - Expected: result.warnings.len() equals `2`
   - Expected: result.doneMessage equals `Claude Code installation completed successfully`
   - Expected: result.onDoneDelayMs equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run success flow with setup and warning messages")
step("Verify: should run success flow with setup and warning messages")
# @req: REQ-TOOLS-InstComm-001
val scenario = InstallScenario.new(true, "stable", "latest", InstallLatestResult.new("1.0.34", true, false), ["Add ~/.local/bin to PATH"], ["removed old npm"], ["removed alias"], "")
val result = runInstallScenario(scenario)
expect(result.finalState).to_equal("success")
expect(result.version).to_equal("1.0.34")
expect(result.channelOrVersion).to_equal("stable")
expect(result.savedChannel).to_equal("stable")
expect(result.analyticsEvent).to_equal("tengu_claude_install_command")
expect(result.hasVersion).to_equal(1)  # oracle: value fixed by the spec contract
expect(result.forced).to_equal(1)  # oracle: value fixed by the spec contract
expect(result.cleanupAttempted).to_equal(true)
expect(result.shellAliasCleanupAttempted).to_equal(true)
expect(result.checkInstallCalled).to_equal(true)
expect(result.warnings.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(result.renderedState).to_contain("Claude Code successfully installed!")
expect(result.renderedState).to_contain("claude --help")
expect(result.doneMessage).to_equal("Claude Code installation completed successfully")
expect(result.onDoneDelayMs).to_equal(2000)  # oracle: value fixed by the spec contract
```

</details>

#### should use settings fallback and current version when install returns no version

- should use settings fallback and current version when install returns no version
- Verify: should use settings fallback and current version when install returns no version
   - Expected: result.finalState equals `success`
   - Expected: result.channelOrVersion equals `stable`
   - Expected: result.version equals `current`
   - Expected: result.savedChannel equals ``
   - Expected: result.hasVersion equals `0`
   - Expected: result.forced equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use settings fallback and current version when install returns no version")
step("Verify: should use settings fallback and current version when install returns no version")
# @req: REQ-TOOLS-InstComm-001
val scenario = InstallScenario.new(false, "", "stable", InstallLatestResult.new("", false, false), [], [], [], "")
val result = runInstallScenario(scenario)
expect(result.finalState).to_equal("success")
expect(result.channelOrVersion).to_equal("stable")
expect(result.version).to_equal("current")
expect(result.savedChannel).to_equal("")
expect(result.hasVersion).to_equal(0)  # oracle: value fixed by the spec contract
expect(result.forced).to_equal(0)  # oracle: value fixed by the spec contract
expect(result.renderedState).to_end_with("Next: Run claude --help to get started")
```

</details>

#### should model lock failure and generic install errors

- should model lock failure and generic install errors
- Verify: should model lock failure and generic install errors
   - Expected: locked.finalState equals `error`
   - Expected: locked.doneMessage equals `Claude Code installation failed`
   - Expected: locked.cleanupAttempted is false
   - Expected: locked.onDoneDelayMs equals `3000`
   - Expected: failed.finalState equals `error`
   - Expected: failed.message equals `network failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model lock failure and generic install errors")
step("Verify: should model lock failure and generic install errors")
# @req: REQ-TOOLS-InstComm-001
val locked = runInstallScenario(InstallScenario.new(false, "latest", "", InstallLatestResult.new("", false, true), [], [], [], ""))
expect(locked.finalState).to_equal("error")
expect(locked.message).to_contain("another process is currently installing Claude")
expect(locked.doneMessage).to_equal("Claude Code installation failed")
expect(locked.cleanupAttempted).to_equal(false)
expect(locked.onDoneDelayMs).to_equal(3000)  # oracle: value fixed by the spec contract

val failed = runInstallScenario(InstallScenario.new(false, "1.0.34", "", InstallLatestResult.new("", false, false), [], [], [], "network failed"))
expect(failed.finalState).to_equal("error")
expect(failed.message).to_equal("network failed")
expect(failed.renderedState).to_contain("Try running with --force")
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
- `REQ-TOOLS-InstComm-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0223c35c1179375f06edfb8e49c20569ab84b6962ec1a365f6c4552fa921f31b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0223c35c1179375f06edfb8e49c20569ab84b6962ec1a365f6c4552fa921f31b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0223c35c1179375f06edfb8e49c20569ab84b6962ec1a365f6c4552fa921f31b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/commands/install_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/install_command_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/install_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/install_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose install command metadata and source size' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose install command metadata and source size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse force and first non-flag target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse force and first non-flag target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model install paths and setup notes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model install paths and setup notes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run success flow with setup and warning messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use settings fallback and current version when install returns no version' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_command_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model lock failure and generic install errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
