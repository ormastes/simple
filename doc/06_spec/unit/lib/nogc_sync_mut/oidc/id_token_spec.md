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

- build a validator expecting client id 'expected-client-id'
- present claims with no audience claim at all
- validation rejects the token because aud is a required claim


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build a validator expecting client id 'expected-client-id'")
val validator = IdTokenValidator.new("https://issuer.example.com", "expected-client-id")
step("present claims with no audience claim at all")
val accepted = validate_accepted(validator, id_token_claims(""))
step("validation rejects the token because aud is a required claim")
# oracle: OIDC Core 1.0 section 2 makes aud REQUIRED; a missing aud must never validate
assert_false(accepted)
```

</details>

#### accepts a token whose audience matches the expected client id

- build a validator expecting client id 'expected-client-id'
- present claims with the matching audience
- validation accepts the token


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build a validator expecting client id 'expected-client-id'")
val validator = IdTokenValidator.new("https://issuer.example.com", "expected-client-id")
step("present claims with the matching audience")
val accepted = validate_accepted(validator, id_token_claims("expected-client-id"))
step("validation accepts the token")
# oracle: exact client-id match is the documented accept case
assert_true(accepted)
```

</details>

#### rejects a token whose audience does not match the expected client id

- build a validator expecting client id 'expected-client-id'
- present claims for a different relying party
- validation rejects the mismatched audience


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build a validator expecting client id 'expected-client-id'")
val validator = IdTokenValidator.new("https://issuer.example.com", "expected-client-id")
step("present claims for a different relying party")
val accepted = validate_accepted(validator, id_token_claims("other-client-id"))
step("validation rejects the mismatched audience")
# oracle: an audience naming another client must never validate for this client id
assert_false(accepted)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_sync_mut/oidc/id_token_spec.spl` |
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

- Canonical SPipe generation for source `2609ed5e85123fc2e306f5aeb5cc8a6fce1ed0de44f13cd2cfa1c5d9261f159c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2609ed5e85123fc2e306f5aeb5cc8a6fce1ed0de44f13cd2cfa1c5d9261f159c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2609ed5e85123fc2e306f5aeb5cc8a6fce1ed0de44f13cd2cfa1c5d9261f159c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/lib/nogc_sync_mut/oidc/id_token_spec.spl
mirror: doc/06_spec/unit/lib/nogc_sync_mut/oidc/id_token_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_sync_mut/oidc/id_token_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_sync_mut/oidc/id_token_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a token with no audience claim when an audience is expected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a token whose audience matches the expected client id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/oidc/id_token_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a token whose audience does not match the expected client id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
