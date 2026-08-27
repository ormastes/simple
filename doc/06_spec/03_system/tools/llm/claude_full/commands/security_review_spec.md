# Claude Full Security Review Command

> Checks modern SSpec parity for the security-review command.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Security Review Command

Checks modern SSpec parity for the security-review command.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/security_review_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the security-review command.

## Scenarios

### Claude full security-review command

#### should expose command metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose command metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose command metadata")
val source = securityReviewSource()
expect(source).to_contain("name: \"security-review\"")
expect(source).to_contain("Review code for security vulnerabilities")
expect(source).to_contain("argumentHint: \"[path]\"")
expect(source).to_contain("supportsNonInteractive: true")
expect(source).to_contain("[\"Read\", \"Grep\", \"Glob\"]")
```

</details>

#### should default to the workspace target

- should default to the workspace target


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should default to the workspace target")
val source = securityReviewSource()
expect(source).to_contain("return \".\"")
expect(source).to_contain("Focus on injection, auth, secrets")
expect(source).to_contain("unsafe file/process access")
expect(source).to_contain("confirmed issues")
```

</details>

#### should review an explicit target and gate untrusted workspaces

- should review an explicit target and gate untrusted workspaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should review an explicit target and gate untrusted workspaces")
val source = securityReviewSource()
expect(source).to_contain("trimmed")
expect(source).to_contain("command.allowedTools")
expect(source).to_contain("queued security review")
expect(source).to_contain("not workspaceTrusted")
expect(source).to_contain("requires a trusted workspace")
```

</details>

#### should expose source size parity

- should expose source size parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source size parity")
val source = securityReviewSource()
expect(source.split("\n").len()).to_be_greater_than(242)
expect(source).to_contain("fn securityReviewSourceLinesModeled() -> i64:")
expect(source).to_contain("243")
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

- Canonical SPipe generation for source `3207208b43249bc439f4d2b0c3a3908079683ac11df2687f3348d6c5e8e569bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3207208b43249bc439f4d2b0c3a3908079683ac11df2687f3348d6c5e8e569bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3207208b43249bc439f4d2b0c3a3908079683ac11df2687f3348d6c5e8e569bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/tools/llm/claude_full/commands/security_review_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/security_review_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/security_review_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/security_review_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:21:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose command metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose command metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should default to the workspace target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should default to the workspace target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should review an explicit target and gate untrusted workspaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should review an explicit target and gate untrusted workspaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/security_review_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose source size parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
