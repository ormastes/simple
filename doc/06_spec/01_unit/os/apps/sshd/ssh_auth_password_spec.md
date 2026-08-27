# Ssh Auth Password Specification

> Tests covering ssh_auth password authentication fail-closed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Auth Password Specification

## Scenarios

### ssh_auth password authentication fail-closed

#### rejects even a fixture password until verifier zeroization is proven

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects even a fixture password until verifier zeroization is proven


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects even a fixture password until verifier zeroization is proven")
val db = configured_demo_users()
expect(db.authenticate_password("root", "simpleos")).to_be(false)
```

</details>

#### rejects a wrong password of equal length

- rejects a wrong password of equal length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong password of equal length")
val db = configured_demo_users()
# "simpleos" is 8 chars; "simpleoz" differs only in the last byte
expect(db.authenticate_password("root", "simpleoz")).to_be(false)
```

</details>

#### rejects a wrong password of different length

- rejects a wrong password of different length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong password of different length")
val db = configured_demo_users()
expect(db.authenticate_password("root", "simple")).to_be(false)
```

</details>

#### rejects an empty password

- rejects an empty password


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty password")
val db = configured_demo_users()
expect(db.authenticate_password("root", "")).to_be(false)
```

</details>

#### rejects an unknown user even with a valid password of another user

- rejects an unknown user even with a valid password of another user


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown user even with a valid password of another user")
val db = configured_demo_users()
expect(db.authenticate_password("nobody", "simpleos")).to_be(false)
```

</details>

#### rejects fixture users without verifier records

- rejects fixture users without verifier records


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fixture users without verifier records")
val db = configured_demo_users()
expect(db.authenticate_password("user", "password")).to_be(false)
expect(db.authenticate_password("user", "simpleos")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ssh_auth password authentication fail-closed.
- ssh_auth password authentication fail-closed

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

- Canonical SPipe generation for source `6ff131fdddcb41e7c5e8f3ece7aa1dd5cb4584d81dbdf38e2416bf7f206c2760`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ff131fdddcb41e7c5e8f3ece7aa1dd5cb4584d81dbdf38e2416bf7f206c2760`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ff131fdddcb41e7c5e8f3ece7aa1dd5cb4584d81dbdf38e2416bf7f206c2760`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/ssh_auth_password_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/ssh_auth_password_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/ssh_auth_password_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects even a fixture password until verifier zeroization is proven' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a wrong password of equal length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a wrong password of different length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
