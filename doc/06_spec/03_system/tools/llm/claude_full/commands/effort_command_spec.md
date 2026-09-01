# Claude Full Effort Command

> Mirrors `tmp/claude/claude-code-main/src/commands/effort` command metadata,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Effort Command

Mirrors `tmp/claude/claude-code-main/src/commands/effort` command metadata,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/effort` command metadata,
argument handling, current-status rendering, and env override messages.

## Scenarios

### Claude full effort command

#### matches command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches command metadata
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `effort`
   - Expected: command.description equals `Set effort level for model usage`
   - Expected: command.argumentHint equals `[low|medium|high|max|auto]`
   - Expected: command.immediate is true
   - Expected: command.loadPath equals `./effort.js`
   - Expected: effortIndexSourceLinesModeled() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches command metadata")
val command = effortCommand(true)

expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("effort")
expect(command.description).to_equal("Set effort level for model usage")
expect(command.argumentHint).to_equal("[low|medium|high|max|auto]")
expect(command.immediate).to_equal(true)
expect(command.loadPath).to_equal("./effort.js")
expect(effortIndexSourceLinesModeled()).to_equal(13)
```

</details>

#### renders help and current effort states

- renders help and current effort states
   - Expected: help.rendered equals `done`
   - Expected: autoState.rendered equals `show-current`
   - Expected: autoState.message equals `Effort level: auto (currently medium)`
   - Expected: current.message equals `Current effort level: high (Comprehensive implementation with extensive testing)`
   - Expected: envAuto.message equals `Effort level: auto (currently high)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders help and current effort states")
val help = callEffort("--help", "", "claude-sonnet-4-5", "", "")
expect(help.rendered).to_equal("done")
expect(help.message).to_contain("Usage: /effort [low|medium|high|max|auto]")
expect(help.message).to_contain("- max: Maximum capability with deepest reasoning (Opus 4.6 only)")

val autoState = callEffort("", "", "claude-sonnet-4-5", "", "")
expect(autoState.rendered).to_equal("show-current")
expect(autoState.message).to_equal("Effort level: auto (currently medium)")

val current = callEffort("status", "high", "claude-sonnet-4-5", "", "")
expect(current.message).to_equal("Current effort level: high (Comprehensive implementation with extensive testing)")

val envAuto = callEffort("current", "high", "claude-opus-4-6", "auto", "")
expect(envAuto.message).to_equal("Effort level: auto (currently high)")
```

</details>

#### sets persistable and session-only effort values

- sets persistable and session-only effort values
   - Expected: low.rendered equals `apply-and-close`
   - Expected: low.message equals `Set effort level to low: Quick, straightforward implementation`
   - Expected: low.hasEffortUpdate is true
   - Expected: low.effortValue equals `low`
   - Expected: low.settingsValue equals `low`
   - Expected: low.loggedEffort equals `low`
   - Expected: max.message equals `Set effort level to max (this session only): Maximum capability with deepest ... (full value in folded executable source)`
   - Expected: max.hasEffortUpdate is true
   - Expected: max.effortValue equals `max`
   - Expected: max.settingsValue equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets persistable and session-only effort values")
val low = callEffort("LOW", "", "claude-sonnet-4-5", "", "")
expect(low.rendered).to_equal("apply-and-close")
expect(low.message).to_equal("Set effort level to low: Quick, straightforward implementation")
expect(low.hasEffortUpdate).to_equal(true)
expect(low.effortValue).to_equal("low")
expect(low.settingsValue).to_equal("low")
expect(low.loggedEffort).to_equal("low")

val max = callEffort("max", "", "claude-opus-4-6", "", "")
expect(max.message).to_equal("Set effort level to max (this session only): Maximum capability with deepest reasoning (Opus 4.6 only)")
expect(max.hasEffortUpdate).to_equal(true)
expect(max.effortValue).to_equal("max")
expect(max.settingsValue).to_equal("")
```

</details>

#### clears effort and reports invalid arguments

- clears effort and reports invalid arguments
   - Expected: unset.message equals `Effort level set to auto`
   - Expected: unset.hasEffortUpdate is true
   - Expected: unset.effortValue equals ``
   - Expected: unset.loggedEffort equals `auto`
   - Expected: invalid.message equals `Invalid argument: turbo. Valid options are: low, medium, high, max, auto`
   - Expected: invalid.hasEffortUpdate is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears effort and reports invalid arguments")
val unset = callEffort("unset", "high", "claude-sonnet-4-5", "", "")
expect(unset.message).to_equal("Effort level set to auto")
expect(unset.hasEffortUpdate).to_equal(true)
expect(unset.effortValue).to_equal("")
expect(unset.loggedEffort).to_equal("auto")

val invalid = callEffort("turbo", "", "claude-sonnet-4-5", "", "")
expect(invalid.message).to_equal("Invalid argument: turbo. Valid options are: low, medium, high, max, auto")
expect(invalid.hasEffortUpdate).to_equal(false)
```

</details>

#### models settings errors and env override warnings

- models settings errors and env override warnings
   - Expected: failure.message equals `Failed to set effort level: disk denied`
   - Expected: failure.hasEffortUpdate is false
   - Expected: overridden.message equals `CLAUDE_CODE_EFFORT_LEVEL=high overrides this session - clear it and medium ta... (full value in folded executable source)`
   - Expected: overridden.hasEffortUpdate is true
   - Expected: overridden.effortValue equals `medium`
   - Expected: overridden.settingsValue equals `medium`
   - Expected: sessionOnly.message equals `Not applied: CLAUDE_CODE_EFFORT_LEVEL=high overrides effort this session, and... (full value in folded executable source)`
   - Expected: sessionOnly.effortValue equals `max`
   - Expected: cleared.message equals `Cleared effort from settings, but CLAUDE_CODE_EFFORT_LEVEL=medium still contr... (full value in folded executable source)`
   - Expected: cleared.hasEffortUpdate is true
   - Expected: cleared.effortValue equals ``
   - Expected: effortSourceLinesModeled() equals `182`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models settings errors and env override warnings")
val failure = callEffort("high", "", "claude-sonnet-4-5", "", "disk denied")
expect(failure.message).to_equal("Failed to set effort level: disk denied")
expect(failure.hasEffortUpdate).to_equal(false)

val overridden = callEffort("medium", "", "claude-sonnet-4-5", "high", "")
expect(overridden.message).to_equal("CLAUDE_CODE_EFFORT_LEVEL=high overrides this session - clear it and medium takes over")
expect(overridden.hasEffortUpdate).to_equal(true)
expect(overridden.effortValue).to_equal("medium")
expect(overridden.settingsValue).to_equal("medium")

val sessionOnly = callEffort("max", "", "claude-opus-4-6", "high", "")
expect(sessionOnly.message).to_equal("Not applied: CLAUDE_CODE_EFFORT_LEVEL=high overrides effort this session, and max is session-only (nothing saved)")
expect(sessionOnly.effortValue).to_equal("max")

val cleared = callEffort("auto", "high", "claude-sonnet-4-5", "medium", "")
expect(cleared.message).to_equal("Cleared effort from settings, but CLAUDE_CODE_EFFORT_LEVEL=medium still controls this session")
expect(cleared.hasEffortUpdate).to_equal(true)
expect(cleared.effortValue).to_equal("")

expect(effortSourceLinesModeled()).to_equal(182)
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

- Canonical SPipe generation for source `d463303f39a03fac847760df3c1f0d548a14e104c3fe84c8dce578566218a6dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d463303f39a03fac847760df3c1f0d548a14e104c3fe84c8dce578566218a6dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d463303f39a03fac847760df3c1f0d548a14e104c3fe84c8dce578566218a6dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/effort_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/effort_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/effort_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders help and current effort states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets persistable and session-only effort values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
