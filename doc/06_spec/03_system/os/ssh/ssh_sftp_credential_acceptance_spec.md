# Ssh Sftp Credential Acceptance Specification

> Tests covering SSH credentials authorize a bounded SFTP protocol session.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Sftp Credential Acceptance Specification

## Scenarios

### SSH credentials authorize a bounded SFTP protocol session

#### admits a configured signed identity and negotiates only SFTP v3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a configured signed identity and negotiates only SFTP v3
   - Expected: response[4] equals `2`
   - Expected: response[8] equals `3`
   - Expected: duplicate[4] equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits a configured signed identity and negotiates only SFTP v3")
val pair = ed25519_keypair_from_seed(acceptance_seed())
val key_blob = acceptance_key_blob(pair.1)
val signature = ed25519_sign(
    pair.0, pair.1,
    acceptance_signed_data(acceptance_session_id(), key_blob))
val request = ssh_parse_auth_request(
    acceptance_auth_request(key_blob, signature)).unwrap()
var users = SshUserDb.new()
users.add_user_identity("operator")
users.add_user_key("operator", key_blob)
val auth = ssh_check_public_key_auth(
    request, acceptance_session_id(), users)
expect(auth.valid).to_be(true)
expect(ssh_sftp_principal_admitted(
    SshSessionState.Interactive, request.username, 1)).to_be(true)
var sftp = SftpSessionV3.new()
val response = sftp.handle_packet([0, 0, 0, 5, 1, 0, 0, 0, 3])
expect(response[4]).to_equal(2)
expect(response[8]).to_equal(3)
val duplicate = sftp.handle_packet([0, 0, 0, 5, 1, 0, 0, 0, 3])
expect(duplicate[4]).to_equal(101)
```

</details>

#### denies SFTP before authentication or without a committed principal

- denies SFTP before authentication or without a committed principal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("denies SFTP before authentication or without a committed principal")
expect(ssh_sftp_principal_admitted(
    SshSessionState.Authentication, "operator", 1)).to_be(false)
expect(ssh_sftp_principal_admitted(
    SshSessionState.Interactive, "", 1)).to_be(false)
```

</details>

#### denies empty and over-capacity channel ownership

- denies empty and over-capacity channel ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("denies empty and over-capacity channel ownership")
expect(ssh_sftp_principal_admitted(
    SshSessionState.Interactive, "operator", 0)).to_be(false)
expect(ssh_sftp_principal_admitted(
    SshSessionState.Interactive, "operator", 257)).to_be(false)
```

</details>

#### rejects tampered authentication before SFTP admission

- rejects tampered authentication before SFTP admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects tampered authentication before SFTP admission")
val pair = ed25519_keypair_from_seed(acceptance_seed())
val key_blob = acceptance_key_blob(pair.1)
var signature = ed25519_sign(
    pair.0, pair.1,
    acceptance_signed_data(acceptance_session_id(), key_blob))
signature[0] = signature[0] ^ 1u8
val request = ssh_parse_auth_request(
    acceptance_auth_request(key_blob, signature)).unwrap()
var users = SshUserDb.new()
users.add_user_identity("operator")
users.add_user_key("operator", key_blob)
val auth = ssh_check_public_key_auth(
    request, acceptance_session_id(), users)
expect(auth.valid).to_be(false)
val principal = if auth.valid: request.username else: ""
expect(ssh_sftp_principal_admitted(
    SshSessionState.Interactive, principal, 1)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSH credentials authorize a bounded SFTP protocol session.
- SSH credentials authorize a bounded SFTP protocol session

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
- `REQ-SSH-CRED-001..004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `718811feac680d53b74f5463586f77330eb7be95f0317af15ceb12e6d8acd832`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `718811feac680d53b74f5463586f77330eb7be95f0317af15ceb12e6d8acd832`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `718811feac680d53b74f5463586f77330eb7be95f0317af15ceb12e6d8acd832`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl
mirror: doc/06_spec/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a configured signed identity and negotiates only SFTP v3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies SFTP before authentication or without a committed principal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies empty and over-capacity channel ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
