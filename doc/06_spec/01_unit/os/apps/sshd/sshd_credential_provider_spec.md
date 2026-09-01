# Sshd Credential Provider Specification

> Tests covering SSHD credential provider is mandatory.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Credential Provider Specification

## Scenarios

### SSHD credential provider is mandatory

#### constructs with no users and refuses startup without provider

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs with no users and refuses startup without provider
   - Expected: daemon.user_db.users.len() equals `0`
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("constructs with no users and refuses startup without provider")
val daemon = SshDaemon.new(2222)
expect(daemon.user_db.users.len()).to_equal(0)
match daemon.start():
    Err(SshdStartError.MissingCredentialProvider):
        expect(true).to_equal(true)
    _: expect(false).to_equal(true)
```

</details>

#### accepts configured public-key identity and host identity without fallback

- accepts configured public-key identity and host identity without fallback
   - Expected: provider.is_valid() is true
   - Expected: daemon.user_db.authenticate_password("operator", "configured-secret") is false
   - Expected: daemon.user_db.authenticate_password("root", "simpleos") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts configured public-key identity and host identity without fallback")
var users = SshUserDb.new()
users.add_user_identity("operator")
users.add_user_key("operator", authorized_key())
val provider = SshdCredentialProvider.new(users, seed32(), seed32())
expect(provider.is_valid()).to_equal(true)
val daemon = SshDaemon.new_with_provider(2222, provider)
expect(daemon.user_db.authenticate_password("operator", "configured-secret")).to_equal(false)
expect(daemon.user_db.authenticate_password("root", "simpleos")).to_equal(false)
```

</details>

#### rejects incomplete provider material

- rejects incomplete provider material
   - Expected: provider.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects incomplete provider material")
var users = SshUserDb.new()
users.add_user_identity("operator")
users.add_user_key("operator", authorized_key())
val provider = SshdCredentialProvider.new(users, [], seed32())
expect(provider.is_valid()).to_equal(false)
```

</details>

#### keeps authentication attempt bound explicit

- keeps authentication attempt bound explicit
   - Expected: MAX_AUTH_ATTEMPTS equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps authentication attempt bound explicit")
expect(MAX_AUTH_ATTEMPTS).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSHD credential provider is mandatory.
- SSHD credential provider is mandatory

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
- `REQ-015`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c9f7a4f60670ecdc70eb73aa4ddce1bd8fb7c4cc5f775ebc3ce2d0b1685e54d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9f7a4f60670ecdc70eb73aa4ddce1bd8fb7c4cc5f775ebc3ce2d0b1685e54d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9f7a4f60670ecdc70eb73aa4ddce1bd8fb7c4cc5f775ebc3ce2d0b1685e54d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with no users and refuses startup without provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts configured public-key identity and host identity without fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects incomplete provider material' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
