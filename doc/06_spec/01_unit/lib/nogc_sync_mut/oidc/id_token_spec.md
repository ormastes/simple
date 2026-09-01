# Id Token Specification

> Tests covering IdTokenValidator.validate_claims.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Id Token Specification

## Scenarios

### IdTokenValidator.validate_claims

#### rejects a token with no audience claim when an audience is expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### accepts a token whose audience matches the expected client id

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = IdTokenValidator.new("https://issuer.example.com", "expected-client-id")
val claims = IdTokenClaims(
    issuer: "https://issuer.example.com",
    subject: "user-123",
    audience: "expected-client-id",
    expiry: 0,
    issued_at: 0,
    nonce: "",
    email: "",
    name: ""
)
val result = validator.validate_claims(claims)
match result:
    case Ok(_):
        pass_do_nothing("correctly accepted matching audience")
    case Err(msg):
        fail_test("expected match to pass, got error: {msg}")
```

</details>

#### rejects a token whose audience does not match the expected client id

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = IdTokenValidator.new("https://issuer.example.com", "expected-client-id")
val claims = IdTokenClaims(
    issuer: "https://issuer.example.com",
    subject: "user-123",
    audience: "other-client-id",
    expiry: 0,
    issued_at: 0,
    nonce: "",
    email: "",
    name: ""
)
val result = validator.validate_claims(claims)
match result:
    case Ok(_):
        fail_test("expected mismatched audience to be rejected")
    case Err(_):
        pass_do_nothing("correctly rejected mismatched audience")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering IdTokenValidator.validate_claims.
- IdTokenValidator.validate_claims

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e31ffd7a7f918d0f6c7fe4593647684752c6b6cba727285279b256b4b257653`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e31ffd7a7f918d0f6c7fe4593647684752c6b6cba727285279b256b4b257653`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e31ffd7a7f918d0f6c7fe4593647684752c6b6cba727285279b256b4b257653`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=70 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:22:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects a token with no audience claim when an audience is expected' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts a token whose audience matches the expected client id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects a token whose audience does not match the expected client id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
