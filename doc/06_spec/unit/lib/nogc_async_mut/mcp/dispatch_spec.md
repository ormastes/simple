# MCP dispatch_wrap Specification

> Registered tool: privilege check runs, output gate runs, audit row logged.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP dispatch_wrap Specification

Registered tool: privilege check runs, output gate runs, audit row logged.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/unit/lib/nogc_async_mut/mcp/dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Registered tool: privilege check runs, output gate runs, audit row logged.
Legacy unregistered tool: still dispatches (no break), emits unregistered-tool
JSON error envelope (fail-closed for registry-using callers).

## Scenarios

### mcp.dispatch

### registered tool

#### AC-5: privilege check runs — denied caller gets EACCES

- AC-5: privilege check runs — denied caller gets EACCES


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: privilege check runs — denied caller gets EACCES")
val reg = DispatchRegistry.new()
reg.register(DispatchEntry.echo(required: id_path_intern("id.user.banking"), level: AuthorityLevel.Sensitive))
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val token = AuthorityToken(
    id_path: id_path_intern("id.user.mail"),
    level: AuthorityLevel.Internal,
    principal: principal,
    trust_source: TrustSource.UserTrusted,
    scope: Scope.persistent(),
    issuer_sig: [1u8])
val reply = dispatch_wrap(reg, "echo", ["hi"], token)
expect reply to_contain "EACCES"
```

</details>

#### AC-5: output gate runs — secret in handler result is redacted

- AC-5: output gate runs — secret in handler result is redacted


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: output gate runs — secret in handler result is redacted")
val reg = DispatchRegistry.new()
reg.register(DispatchEntry.leak_aws(required: id_path_intern("id.user.public"), level: AuthorityLevel.Public))
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal,
    trust_source: TrustSource.UserTrusted,
    scope: Scope.persistent(),
    issuer_sig: [1u8])
val reply = dispatch_wrap(reg, "leak_aws", [], token)
expect reply to_contain "REDACTED"
```

</details>

#### AC-5: audit row logged for every registered invocation

- AC-5: audit row logged for every registered invocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: audit row logged for every registered invocation")
val reg = DispatchRegistry.new_for_test()
reg.register(DispatchEntry.echo(required: id_path_intern("id.user.public"), level: AuthorityLevel.Public))
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal,
    trust_source: TrustSource.UserTrusted,
    scope: Scope.persistent(),
    issuer_sig: [1u8])
dispatch_wrap(reg, "echo", ["hi"], token)
expect(test_audit_sink_size(reg)).to_be_greater_than(0)
val reply = dispatch_wrap(reg, "echo", ["ok"], token)
expect reply to_contain "\"body\":\"ok\""
```

</details>

### unregistered tool

#### AC-5: returns unregistered_tool error envelope (fail-closed)

- AC-5: returns unregistered_tool error envelope (fail-closed)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns unregistered_tool error envelope (fail-closed)")
val reg = DispatchRegistry.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal,
    trust_source: TrustSource.UserTrusted,
    scope: Scope.persistent(),
    issuer_sig: [1u8])
val reply = dispatch_wrap(reg, "unknown_tool", [], token)
expect reply to_contain "unregistered_tool"
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c4a3b2c39d63abc24e3c6143e6d3221e08f74e1318ca20f4fe0c8ecc31e1739d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4a3b2c39d63abc24e3c6143e6d3221e08f74e1318ca20f4fe0c8ecc31e1739d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4a3b2c39d63abc24e3c6143e6d3221e08f74e1318ca20f4fe0c8ecc31e1739d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/mcp/dispatch_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/mcp/dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/mcp/dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/mcp/dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/mcp/dispatch_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: privilege check runs — denied caller gets EACCES' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/mcp/dispatch_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: output gate runs — secret in handler result is redacted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/mcp/dispatch_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: audit row logged for every registered invocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
