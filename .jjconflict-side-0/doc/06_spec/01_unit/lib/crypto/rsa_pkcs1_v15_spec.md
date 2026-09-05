# Rsa Pkcs1 V15 Specification

> Tests covering RSA-SHA-256 PKCS#1 v1.5 pure-Simple round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Pkcs1 V15 Specification

## Scenarios

### RSA-SHA-256 PKCS#1 v1.5 pure-Simple round-trip

#### signs empty message and verifies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- signs empty message and verifies
   - Expected: rsa_sha256_verify(_spki(), _msg_empty(), _sig_empty()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signs empty message and verifies")
expect(rsa_sha256_verify(_spki(), _msg_empty(), _sig_empty())).to_equal(true)
```

</details>

#### signature is non-empty for empty message

- signature is non-empty for empty message
   - Expected: rsa_sig_valid(_sig_empty()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signature is non-empty for empty message")
expect(rsa_sig_valid(_sig_empty())).to_equal(true)
```

</details>

#### signature is 256 bytes for RSA-2048 key

- signature is 256 bytes for RSA-2048 key
   - Expected: _sig_hello().len().to_i64() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signature is 256 bytes for RSA-2048 key")
# Modulus is 2048 bits = 256 bytes; signature must match modulus length
expect(_sig_hello().len().to_i64()).to_equal(256)
```

</details>

#### signs 'Hello' and verifies

- signs 'Hello' and verifies
   - Expected: rsa_sha256_verify(_spki(), _msg_hello(), _sig_hello()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signs 'Hello' and verifies")
expect(rsa_sha256_verify(_spki(), _msg_hello(), _sig_hello())).to_equal(true)
```

</details>

#### signs 32-byte message and verifies

- signs 32-byte message and verifies
   - Expected: rsa_sha256_verify(_spki(), _msg_32bytes(), _sig_32bytes()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signs 32-byte message and verifies")
expect(rsa_sha256_verify(_spki(), _msg_32bytes(), _sig_32bytes())).to_equal(true)
```

</details>

#### signs 256-byte message and verifies

- signs 256-byte message and verifies
   - Expected: rsa_sha256_verify(_spki(), _msg_256bytes(), _sig_256bytes()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signs 256-byte message and verifies")
expect(rsa_sha256_verify(_spki(), _msg_256bytes(), _sig_256bytes())).to_equal(true)
```

</details>

#### signs 1024-byte message and verifies

- signs 1024-byte message and verifies
   - Expected: rsa_sha256_verify(_spki(), _msg_1024bytes(), _sig_1024bytes()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("signs 1024-byte message and verifies")
expect(rsa_sha256_verify(_spki(), _msg_1024bytes(), _sig_1024bytes())).to_equal(true)
```

</details>

#### rejects a signature with last byte flipped

- rejects a signature with last byte flipped
   - Expected: rsa_sha256_verify(_spki(), _msg_hello(), _corrupted_sig_hello()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a signature with last byte flipped")
expect(rsa_sha256_verify(_spki(), _msg_hello(), _corrupted_sig_hello())).to_equal(false)
```

</details>

#### rejects signature when message differs (Hello vs hello)

- rejects signature when message differs (Hello vs hello)
   - Expected: rsa_sha256_verify(_spki(), _different_msg_hello(), _sig_hello()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects signature when message differs (Hello vs hello)")
# Valid signature for 'Hello' must not verify against 'hello'
expect(rsa_sha256_verify(_spki(), _different_msg_hello(), _sig_hello())).to_equal(false)
```

</details>

#### rejects empty signature against valid message

- rejects empty signature against valid message
   - Expected: rsa_sha256_verify(_spki(), _msg_hello(), empty_sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects empty signature against valid message")
val empty_sig: [u8] = []
expect(rsa_sha256_verify(_spki(), _msg_hello(), empty_sig)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RSA-SHA-256 PKCS#1 v1.5 pure-Simple round-trip.
- RSA-SHA-256 PKCS#1 v1.5 pure-Simple round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7bba2c385dd5413d21e35c913d220637e39a9364de70f6dc914161fb51df4fe2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bba2c385dd5413d21e35c913d220637e39a9364de70f6dc914161fb51df4fe2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bba2c385dd5413d21e35c913d220637e39a9364de70f6dc914161fb51df4fe2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/rsa_pkcs1_v15_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/rsa_pkcs1_v15_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/rsa_pkcs1_v15_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signs empty message and verifies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signature is non-empty for empty message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signature is 256 bytes for RSA-2048 key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
