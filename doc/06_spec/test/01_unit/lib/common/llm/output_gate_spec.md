# LLM Output Gate Specification

> Clean text → Pass. AWS-key-shape text → Hold. PII (phone/email) → Hold.

<!-- sdn-diagram:id=output_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=output_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

output_gate_spec -> std
output_gate_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=output_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/common/llm/output_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Clean text → Pass. AWS-key-shape text → Hold. PII (phone/email) → Hold.
`filter_response_body` on Hold returns redacted bytes and emits notify +
audit row (via reused audit_log).

## Scenarios

### OutputGate

### scan_and_gate

#### AC-5: clean text passes

- id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = OutputGate.default()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val body = "AKIA-1234567890ABCDEF leaked".bytes()
val decision = gate.scan_and_gate(body, token)
expect decision.kind to_equal "Hold"
val has_reasons = decision.reasons.len() > 0
expect has_reasons to_equal true
```

</details>

#### AC-5: phone-number PII triggers Hold

- id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- id path: id path intern
- expect out len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
val notify_ok = test_notify_sink_size(gate) > 0
val audit_ok = test_audit_sink_size(gate) > 0
expect notify_ok to_equal true
expect audit_ok to_equal true
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
