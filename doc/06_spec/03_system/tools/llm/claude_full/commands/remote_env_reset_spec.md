# Claude Full Remote Env and Reset Limits Commands

> Checks modern SSpec parity for tiny remote env and reset limits rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Remote Env and Reset Limits Commands

Checks modern SSpec parity for tiny remote env and reset limits rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for tiny remote env and reset limits rows.

## Scenarios

### Claude full remote env reset commands

#### should expose command names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose command names
   - Expected: remoteEnvCommandName() equals `remote-env`
   - Expected: remoteEnvIndexName() equals `remote-env`
   - Expected: resetLimitsCommandName() equals `reset-limits`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose command names")
expect(remoteEnvCommandName()).to_equal("remote-env")
expect(remoteEnvIndexName()).to_equal("remote-env")
expect(resetLimitsCommandName()).to_equal("reset-limits")
```

</details>

#### should expose source sizes

- should expose source sizes
   - Expected: remoteEnvIndexSourceLinesModeled() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source sizes")
expect(remoteEnvIndexSourceLinesModeled()).to_equal(15)
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

- Canonical SPipe generation for source `f649ef8d94c33b542003ac966b7817027b78899c9c46ae4598b14aa8a25c5102`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f649ef8d94c33b542003ac966b7817027b78899c9c46ae4598b14aa8a25c5102`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f649ef8d94c33b542003ac966b7817027b78899c9c46ae4598b14aa8a25c5102`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose command names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose command names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose source sizes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose source sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
