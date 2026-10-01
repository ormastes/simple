# LLM Output Gate Specification

> Clean text → Pass. AWS-key-shape text → Hold. PII (phone/email) → Hold.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Output Gate Specification

Clean text → Pass. AWS-key-shape text → Hold. PII (phone/email) → Hold.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/unit/lib/common/llm/output_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Clean text → Pass. AWS-key-shape text → Hold. PII (phone/email) → Hold.
`filter_response_body` on Hold returns redacted bytes and emits notify +
audit row (via reused audit_log).

## Scenarios

### OutputGate

### scan_and_gate

#### AC-5: clean text passes

- AC-5: clean text passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: clean text passes")
val gate = OutputGate.default()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val decision = gate.scan_and_gate("hello world".bytes(), token)
expect decision.kind to_equal "Pass"
```

</details>

#### AC-5: AWS key shape is Hold with non-empty reasons

- AC-5: AWS key shape is Hold with non-empty reasons


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: AWS key shape is Hold with non-empty reasons")
val gate = OutputGate.default()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val body = "AKIA-1234567890ABCDEF leaked".bytes()
val decision = gate.scan_and_gate(body, token)
expect decision.kind to_equal "Hold"
expect decision.reasons.len() to_be_greater_than 0
```

</details>

#### AC-5: phone-number PII triggers Hold

- AC-5: phone-number PII triggers Hold


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: phone-number PII triggers Hold")
val gate = OutputGate.default()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val decision = gate.scan_and_gate("call me at 415-555-0123".bytes(), token)
expect decision.kind to_equal "Hold"
```

</details>

#### AC-5: email PII triggers Hold

- AC-5: email PII triggers Hold


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: email PII triggers Hold")
val gate = OutputGate.default()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val decision = gate.scan_and_gate("contact bob@example.com".bytes(), token)
expect decision.kind to_equal "Hold"
```

</details>

### filter_response_body

#### AC-5: Pass returns passthrough bytes

- AC-5: Pass returns passthrough bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: Pass returns passthrough bytes")
val gate = OutputGate.default()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val body = "no secrets here".bytes()
val out = gate.filter_response_body(body, token)
expect out.len() to_equal body.len()
```

</details>

#### AC-5: Hold returns redacted bytes, emits notify + audit

- AC-5: Hold returns redacted bytes, emits notify + audit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: Hold returns redacted bytes, emits notify + audit")
val gate = OutputGate.default_for_test()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val body = "AKIA-1234567890ABCDEF leaked".bytes()
val out = gate.filter_response_body(body, token)
val equal = (out.len() == body.len())
expect equal to_equal false
expect test_notify_sink_size(gate) to_be_greater_than 0
expect test_audit_sink_size(gate) to_be_greater_than 0
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d77cb15a23b6d7dd989579fb2fe01e982e3e56efd3a94024321324d70b29ee3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d77cb15a23b6d7dd989579fb2fe01e982e3e56efd3a94024321324d70b29ee3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d77cb15a23b6d7dd989579fb2fe01e982e3e56efd3a94024321324d70b29ee3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/llm/output_gate_spec.spl
mirror: doc/06_spec/unit/lib/common/llm/output_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/llm/output_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/llm/output_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/llm/output_gate_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: clean text passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/llm/output_gate_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: AWS key shape is Hold with non-empty reasons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/llm/output_gate_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: phone-number PII triggers Hold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
