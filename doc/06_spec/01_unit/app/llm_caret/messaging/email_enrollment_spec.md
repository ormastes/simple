# Email Enrollment Specification

> Tests covering primitive local email enrollment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Email Enrollment Specification

## Scenarios

### primitive local email enrollment

#### stores only a token hash and creates one local account after verification

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores only a token hash and creates one local account after verification
   - Expected: issued.accepted is true
   - Expected: service.invites.len() equals `1`
   - Expected: service.invites[0].email equals `human@example.com`
   - Expected: service.invites[0].token_hash equals `enrollment_hash(issued.delivery_token)`
   - Expected: service.invites[0].token_hash does not contain `issued.delivery_token`
   - Expected: accepted.accepted is true
   - Expected: service.accounts.len() equals `1`
   - Expected: service.accept_token(issued.delivery_token, 3000).error equals `invite_already_used`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stores only a token hash and creates one local account after verification")
var service = EnrollmentService.empty()
val issued = service.issue_invite("invite-1", "Human@Example.com",
    "local-secret-capability", 1000, 60000, 3)
expect(issued.accepted).to_equal(true)
expect(issued.delivery_token.len()).to_be_greater_than(16)
expect(service.invites.len()).to_equal(1)
expect(service.invites[0].email).to_equal("human@example.com")
expect(service.invites[0].token_hash).to_equal(enrollment_hash(issued.delivery_token))
expect(service.invites[0].token_hash.contains(issued.delivery_token)).to_equal(false)
val accepted = service.accept_token(issued.delivery_token, 2000)
expect(accepted.accepted).to_equal(true)
expect(service.accounts.len()).to_equal(1)
expect(service.accept_token(issued.delivery_token, 3000).error).to_equal("invite_already_used")
```

</details>

#### expires tokens and limits invalid attempts without creating accounts

- expires tokens and limits invalid attempts without creating accounts
   - Expected: service.accept_invite("invite-2", "wrong-one", 2000).error equals `invite_token_invalid`
   - Expected: service.accept_invite("invite-2", "wrong-two", 3000).error equals `invite_token_invalid`
   - Expected: service.accept_invite("invite-2", issued.delivery_token, 4000).error equals `invite_attempt_limit`
   - Expected: service.accounts.len() equals `0`
   - Expected: expired.accept_token(short.delivery_token, 61000).error equals `invite_expired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("expires tokens and limits invalid attempts without creating accounts")
var service = EnrollmentService.empty()
val issued = service.issue_invite("invite-2", "human@example.com",
    "local-secret-capability", 1000, 60000, 2)
expect(service.accept_invite("invite-2", "wrong-one", 2000).error).to_equal("invite_token_invalid")
expect(service.accept_invite("invite-2", "wrong-two", 3000).error).to_equal("invite_token_invalid")
expect(service.accept_invite("invite-2", issued.delivery_token, 4000).error).to_equal("invite_attempt_limit")
expect(service.accounts.len()).to_equal(0)
var expired = EnrollmentService.empty()
val short = expired.issue_invite("invite-3", "other@example.com",
    "local-secret-capability", 1000, 60000, 2)
expect(expired.accept_token(short.delivery_token, 61000).error).to_equal("invite_expired")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/email_enrollment_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering primitive local email enrollment.
- primitive local email enrollment

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e0dcc032675f9f1853269f9aec17e06bd26c62507bf00b30cc4d890f7cc4047`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e0dcc032675f9f1853269f9aec17e06bd26c62507bf00b30cc4d890f7cc4047`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e0dcc032675f9f1853269f9aec17e06bd26c62507bf00b30cc4d890f7cc4047`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/messaging/email_enrollment_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/email_enrollment_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/messaging/email_enrollment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/email_enrollment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/email_enrollment_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/email_enrollment_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores only a token hash and creates one local account after verification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/email_enrollment_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expires tokens and limits invalid attempts without creating accounts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
