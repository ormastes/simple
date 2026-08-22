# sshd_credential_provider_spec

> Verifies the sshd credential provider behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sshd_credential_provider_spec

Verifies the sshd credential provider behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the sshd credential provider behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SSHD credential provider is mandatory

#### constructs with no users and refuses startup without provider

- Verify: constructs with no users and refuses startup without provider
   - Expected: daemon.user_db.users.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-015
step("Verify: constructs with no users and refuses startup without provider")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val daemon = SshDaemon.new(2222)
expect(daemon.user_db.users.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
match daemon.start():
    Err(SshdStartError.MissingCredentialProvider):
        expect(true).to_equal(true)
    _: expect(false).to_equal(true)
```

</details>

#### accepts configured public-key identity and host identity without fallback

- Verify: accepts configured public-key identity and host identity without fallback
   - Expected: provider.is_valid() is true
   - Expected: daemon.user_db.authenticate_password("operator", "configured-secret") is false
   - Expected: daemon.user_db.authenticate_password("root", "simpleos") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-015
step("Verify: accepts configured public-key identity and host identity without fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects incomplete provider material
   - Expected: provider.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-015
step("Verify: rejects incomplete provider material")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var users = SshUserDb.new()
users.add_user_identity("operator")
users.add_user_key("operator", authorized_key())
val provider = SshdCredentialProvider.new(users, [], seed32())
expect(provider.is_valid()).to_equal(false)
```

</details>

#### keeps authentication attempt bound explicit

- Verify: keeps authentication attempt bound explicit
   - Expected: MAX_AUTH_ATTEMPTS equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-015
step("Verify: keeps authentication attempt bound explicit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(MAX_AUTH_ATTEMPTS).to_equal(6)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aee92f727aa1cf0f6404fd69d58a3ef1bffa27d1973a8796b2de545af1786568`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aee92f727aa1cf0f6404fd69d58a3ef1bffa27d1973a8796b2de545af1786568`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aee92f727aa1cf0f6404fd69d58a3ef1bffa27d1973a8796b2de545af1786568`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/apps/sshd/sshd_credential_provider_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/sshd_credential_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
