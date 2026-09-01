# Claude Full Install Slack App Command

> Checks modern SSpec parity for install-slack-app descriptors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install Slack App Command

Checks modern SSpec parity for install-slack-app descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for install-slack-app descriptors.

## Scenarios

### Claude full install slack app command

#### should expose install slack command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose install slack command metadata
   - Expected: installSlackAppCommandName() equals `install-slack-app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose install slack command metadata")
expect(installSlackAppCommandName()).to_equal("install-slack-app")
expect(installSlackAppCommand().description).to_contain("Slack")
expect(installSlackAppCommand().url).to_contain("slack.com")
```

</details>

#### should format workspace messages

- should format workspace messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should format workspace messages")
expect(installSlackAppMessage("")).to_contain("installation")
expect(installSlackAppMessage("eng")).to_contain("eng")
```

</details>

#### should expose source sizes

- should expose source sizes
   - Expected: installSlackAppSourceLinesModeled() equals `30`
   - Expected: installSlackAppIndexSourceLinesModeled() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source sizes")
expect(installSlackAppSourceLinesModeled()).to_equal(30)
expect(installSlackAppIndexSourceLinesModeled()).to_equal(12)
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

- Canonical SPipe generation for source `91819af8b46770ca8804208b148c237a493ce3bdfc0d0bd951cba8aebc374cd5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91819af8b46770ca8804208b148c237a493ce3bdfc0d0bd951cba8aebc374cd5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91819af8b46770ca8804208b148c237a493ce3bdfc0d0bd951cba8aebc374cd5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/install_slack_app_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/install_slack_app_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/install_slack_app_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose install slack command metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose install slack command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format workspace messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format workspace messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose source sizes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose source sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
