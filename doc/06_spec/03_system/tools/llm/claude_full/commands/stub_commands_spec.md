# Claude Full Stub Commands

> Mirrors one-line Claude command index files that export hidden disabled stub

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Stub Commands

Mirrors one-line Claude command index files that export hidden disabled stub

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors one-line Claude command index files that export hidden disabled stub
commands.

## Scenarios

### Claude full stub command indexes

#### should expose hidden disabled bughunter, issue, and onboarding commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose hidden disabled bughunter, issue, and onboarding commands
- Load the first stub command batch
- Check Claude's shared stub-command metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose hidden disabled bughunter, issue, and onboarding commands")
step("Load the first stub command batch")
val bughunter = bughunterCommand()
val issue = issueCommand()
val onboarding = onboardingCommand()

step("Check Claude's shared stub-command metadata")
assert_stub_command(bughunter.name, bughunter.isHidden, bughunter.isEnabled())
assert_stub_command(issue.name, issue.isHidden, issue.isEnabled())
assert_stub_command(onboarding.name, onboarding.isHidden, onboarding.isEnabled())
```

</details>

#### should expose hidden disabled share, summary, and teleport commands

- should expose hidden disabled share, summary, and teleport commands
- Load the second stub command batch
- Check Claude's shared stub-command metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose hidden disabled share, summary, and teleport commands")
step("Load the second stub command batch")
val share = shareCommand()
val summary = summaryCommand()
val teleport = teleportCommand()

step("Check Claude's shared stub-command metadata")
assert_stub_command(share.name, share.isHidden, share.isEnabled())
assert_stub_command(summary.name, summary.isHidden, summary.isEnabled())
assert_stub_command(teleport.name, teleport.isHidden, teleport.isEnabled())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `f92a9450286cfe8c8a3a7977c3557850f0b7e4910d7a8fa9b802d7d28b0baac0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f92a9450286cfe8c8a3a7977c3557850f0b7e4910d7a8fa9b802d7d28b0baac0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f92a9450286cfe8c8a3a7977c3557850f0b7e4910d7a8fa9b802d7d28b0baac0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/stub_commands_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/stub_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/stub_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose hidden disabled bughunter, issue, and onboarding commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose hidden disabled bughunter, issue, and onboarding commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose hidden disabled share, summary, and teleport commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose hidden disabled share, summary, and teleport commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
