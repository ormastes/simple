# Cert Verify Ed25519 Specification

> Tests covering verify_certificate_verify_msg_scheme Ed25519 (0x0807), verify_certificate_verify_msg shim.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cert Verify Ed25519 Specification

## Scenarios

### verify_certificate_verify_msg_scheme Ed25519 (0x0807)

#### verifies a valid Ed25519 CertificateVerify message

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- verifies a valid Ed25519 CertificateVerify message
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies a valid Ed25519 CertificateVerify message")
val pubkey = _pubkey_a()
val sig = _sign_content()
val result = verify_certificate_verify_msg_scheme(pubkey, 0x0807u16, _transcript_hash(), sig)
if val CertVerifyResult.Ok = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects signature verified under a different public key

- rejects signature verified under a different public key
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects signature verified under a different public key")
val other_pubkey = _pubkey_b()
val sig = _sign_content()
val result = verify_certificate_verify_msg_scheme(other_pubkey, 0x0807u16, _transcript_hash(), sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects a signature with a flipped byte

- rejects a signature with a flipped byte
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a signature with a flipped byte")
val pubkey = _pubkey_a()
val sig = _sign_content()
val bad_sig = _flip_byte_at(sig, 4u64)
val result = verify_certificate_verify_msg_scheme(pubkey, 0x0807u16, _transcript_hash(), bad_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects an unknown sig_scheme

- rejects an unknown sig_scheme
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown sig_scheme")
val pubkey = _pubkey_a()
val sig = _sign_content()
val result = verify_certificate_verify_msg_scheme(pubkey, 0x0000u16, _transcript_hash(), sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

### verify_certificate_verify_msg shim

#### delegates to Ed25519 and accepts a valid signature

- delegates to Ed25519 and accepts a valid signature
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delegates to Ed25519 and accepts a valid signature")
val pubkey = _pubkey_a()
val sig = _sign_content()
val result = verify_certificate_verify_msg(pubkey, _transcript_hash(), sig)
if val CertVerifyResult.Ok = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### delegates to Ed25519 and rejects a bad signature

- delegates to Ed25519 and rejects a bad signature
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delegates to Ed25519 and rejects a bad signature")
val pubkey = _pubkey_a()
val sig = _sign_content()
val bad_sig = _flip_byte_at(sig, 0u64)
val result = verify_certificate_verify_msg(pubkey, _transcript_hash(), bad_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/cert_verify_ed25519_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering verify_certificate_verify_msg_scheme Ed25519 (0x0807), verify_certificate_verify_msg shim.
- verify_certificate_verify_msg_scheme Ed25519 (0x0807)
- verify_certificate_verify_msg shim

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

- Canonical SPipe generation for source `038cfc16bfd85b348c6ca7cf32d50e8423c5e661e6757ad3148d769e3af31c0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `038cfc16bfd85b348c6ca7cf32d50e8423c5e661e6757ad3148d769e3af31c0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `038cfc16bfd85b348c6ca7cf32d50e8423c5e661e6757ad3148d769e3af31c0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/cert_verify_ed25519_spec.spl
mirror: doc/06_spec/unit/os/tls13/cert_verify_ed25519_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/cert_verify_ed25519_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/cert_verify_ed25519_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/cert_verify_ed25519_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies a valid Ed25519 CertificateVerify message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/cert_verify_ed25519_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects signature verified under a different public key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/cert_verify_ed25519_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a signature with a flipped byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
