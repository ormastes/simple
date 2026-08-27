# RSA-PSS Verify FFI Specification

> Structural tests for the three RSA-PSS verify FFI wrappers landed in commit `a2c5361f5e04`:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RSA-PSS Verify FFI Specification

Structural tests for the three RSA-PSS verify FFI wrappers landed in commit `a2c5361f5e04`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/os/os_rt_rsa_pss_verify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Structural tests for the three RSA-PSS verify FFI wrappers landed in commit
`a2c5361f5e04`:

  - `rsa_pss_sha256_verify_native(pubkey, msg, sig) -> bool`
  - `rsa_pss_sha384_verify_native(pubkey, msg, sig) -> bool`
  - `rsa_pss_sha512_verify_native(pubkey, msg, sig) -> bool`

Goal: reference-cross-check structure (design option b) so when compiled mode
lands, tests actually exercise the FFI.  In interpreter mode, `it` blocks reach
"unknown extern function: rt_rsa_pss_sha*_verify" — that is the expected state
until native compilation runs the externs.

`bin/simple check` gives load-time type-check coverage today.

tag: slow, system, crypto

## Scenarios

### rsa_pss_sha256_verify_native

#### accepts a valid PSS-SHA256 signature

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a valid PSS-SHA256 signature
   - Expected: rsa_pss_sha256_verify_native(spki, msg, sig) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts a valid PSS-SHA256 signature")
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val msg  = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha256_verify_native(spki, msg, sig)).to_equal(true)
```

</details>

#### rejects a tampered PSS-SHA256 signature

- rejects a tampered PSS-SHA256 signature
   - Expected: rsa_pss_sha256_verify_native(spki, msg, sig_bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a tampered PSS-SHA256 signature")
val spki        = hex_to_bytes(RSA_SPKI_HEX)
val sig_original = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val sig_bad     = _flip_byte(sig_original, 10)
val msg         = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha256_verify_native(spki, msg, sig_bad)).to_equal(false)
```

</details>

#### rejects a valid PSS-SHA256 signature with wrong message

- rejects a valid PSS-SHA256 signature with wrong message
   - Expected: rsa_pss_sha256_verify_native(spki, msg, sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a valid PSS-SHA256 signature with wrong message")
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val msg  = hex_to_bytes(WRONG_MSG_HEX)
expect(rsa_pss_sha256_verify_native(spki, msg, sig)).to_equal(false)
```

</details>

#### rejects a malformed SPKI for PSS-SHA256

- rejects a malformed SPKI for PSS-SHA256
   - Expected: rsa_pss_sha256_verify_native(bad_spki, msg, sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a malformed SPKI for PSS-SHA256")
val bad_spki = [0x30u8, 0x01]
val sig      = hex_to_bytes(VALID_PSS_SIG_SHA256_HEX)
val msg      = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha256_verify_native(bad_spki, msg, sig)).to_equal(false)
```

</details>

### rsa_pss_sha384_verify_native

#### accepts a valid PSS-SHA384 signature

- accepts a valid PSS-SHA384 signature
   - Expected: rsa_pss_sha384_verify_native(spki, msg, sig) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts a valid PSS-SHA384 signature")
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val msg  = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha384_verify_native(spki, msg, sig)).to_equal(true)
```

</details>

#### rejects a tampered PSS-SHA384 signature

- rejects a tampered PSS-SHA384 signature
   - Expected: rsa_pss_sha384_verify_native(spki, msg, sig_bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a tampered PSS-SHA384 signature")
val spki         = hex_to_bytes(RSA_SPKI_HEX)
val sig_original = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val sig_bad      = _flip_byte(sig_original, 10)
val msg          = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha384_verify_native(spki, msg, sig_bad)).to_equal(false)
```

</details>

#### rejects a valid PSS-SHA384 signature with wrong message

- rejects a valid PSS-SHA384 signature with wrong message
   - Expected: rsa_pss_sha384_verify_native(spki, msg, sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a valid PSS-SHA384 signature with wrong message")
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val msg  = hex_to_bytes(WRONG_MSG_HEX)
expect(rsa_pss_sha384_verify_native(spki, msg, sig)).to_equal(false)
```

</details>

#### rejects a malformed SPKI for PSS-SHA384

- rejects a malformed SPKI for PSS-SHA384
   - Expected: rsa_pss_sha384_verify_native(bad_spki, msg, sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a malformed SPKI for PSS-SHA384")
val bad_spki = [0x30u8, 0x01]
val sig      = hex_to_bytes(VALID_PSS_SIG_SHA384_HEX)
val msg      = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha384_verify_native(bad_spki, msg, sig)).to_equal(false)
```

</details>

### rsa_pss_sha512_verify_native

#### accepts a valid PSS-SHA512 signature

- accepts a valid PSS-SHA512 signature
   - Expected: rsa_pss_sha512_verify_native(spki, msg, sig) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts a valid PSS-SHA512 signature")
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val msg  = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha512_verify_native(spki, msg, sig)).to_equal(true)
```

</details>

#### rejects a tampered PSS-SHA512 signature

- rejects a tampered PSS-SHA512 signature
   - Expected: rsa_pss_sha512_verify_native(spki, msg, sig_bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a tampered PSS-SHA512 signature")
val spki         = hex_to_bytes(RSA_SPKI_HEX)
val sig_original = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val sig_bad      = _flip_byte(sig_original, 10)
val msg          = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha512_verify_native(spki, msg, sig_bad)).to_equal(false)
```

</details>

#### rejects a valid PSS-SHA512 signature with wrong message

- rejects a valid PSS-SHA512 signature with wrong message
   - Expected: rsa_pss_sha512_verify_native(spki, msg, sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a valid PSS-SHA512 signature with wrong message")
val spki = hex_to_bytes(RSA_SPKI_HEX)
val sig  = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val msg  = hex_to_bytes(WRONG_MSG_HEX)
expect(rsa_pss_sha512_verify_native(spki, msg, sig)).to_equal(false)
```

</details>

#### rejects a malformed SPKI for PSS-SHA512

- rejects a malformed SPKI for PSS-SHA512
   - Expected: rsa_pss_sha512_verify_native(bad_spki, msg, sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a malformed SPKI for PSS-SHA512")
val bad_spki = [0x30u8, 0x01]
val sig      = hex_to_bytes(VALID_PSS_SIG_SHA512_HEX)
val msg      = hex_to_bytes(PSS_MSG_HEX)
expect(rsa_pss_sha512_verify_native(bad_spki, msg, sig)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e8db812d90c21f09999eb086dc6f7a1c0ac7a441dda0764ee0289a1057d19324`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8db812d90c21f09999eb086dc6f7a1c0ac7a441dda0764ee0289a1057d19324`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8db812d90c21f09999eb086dc6f7a1c0ac7a441dda0764ee0289a1057d19324`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/os_rt_rsa_pss_verify_spec.spl
mirror: doc/06_spec/03_system/os/os_rt_rsa_pss_verify_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_rt_rsa_pss_verify_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_rt_rsa_pss_verify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_rt_rsa_pss_verify_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a valid PSS-SHA256 signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_rt_rsa_pss_verify_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a tampered PSS-SHA256 signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_rt_rsa_pss_verify_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a valid PSS-SHA256 signature with wrong message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
