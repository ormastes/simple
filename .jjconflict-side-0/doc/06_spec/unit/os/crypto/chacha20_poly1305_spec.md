# Chacha20 Poly1305 Specification

> Tests covering ChaCha20-Poly1305 RFC 8439 §2.8.2 AEAD KAT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Specification

## Scenarios

### ChaCha20-Poly1305 RFC 8439 §2.8.2 AEAD KAT

#### encrypt produces correct total output length (114 ciphertext + 16 tag = 130 bytes)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encrypt produces correct total output length (114 ciphertext + 16 tag = 130 bytes)
   - Expected: out.len() equals `130`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces correct total output length (114 ciphertext + 16 tag = 130 bytes)")
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
expect(out.len()).to_equal(130)
```

</details>

#### encrypt produces correct ciphertext bytes (first 16)

- encrypt produces correct ciphertext bytes (first 16)
   - Expected: got equals `exp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces correct ciphertext bytes (first 16)")
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 0, 16)
val exp = _slice(_expected_ciphertext(), 0, 16)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct ciphertext bytes (bytes 16-32)

- encrypt produces correct ciphertext bytes (bytes 16-32)
   - Expected: got equals `exp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces correct ciphertext bytes (bytes 16-32)")
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 16, 32)
val exp = _slice(_expected_ciphertext(), 16, 32)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct ciphertext bytes (bytes 32-64)

- encrypt produces correct ciphertext bytes (bytes 32-64)
   - Expected: got equals `exp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces correct ciphertext bytes (bytes 32-64)")
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 32, 64)
val exp = _slice(_expected_ciphertext(), 32, 64)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct ciphertext bytes (bytes 64-114)

- encrypt produces correct ciphertext bytes (bytes 64-114)
   - Expected: got equals `exp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces correct ciphertext bytes (bytes 64-114)")
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 64, 114)
val exp = _slice(_expected_ciphertext(), 64, 114)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct Poly1305 tag (last 16 bytes)

- encrypt produces correct Poly1305 tag (last 16 bytes)
   - Expected: got_tag equals `_expected_tag()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt produces correct Poly1305 tag (last 16 bytes)")
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got_tag = _slice(out, 114, 130)
expect(got_tag).to_equal(_expected_tag())
```

</details>

#### decrypt with correct tag succeeds

- decrypt with correct tag succeeds
   - Expected: _decrypt_ok(res) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt with correct tag succeeds")
val res = chacha20_poly1305_decrypt(_key(), _nonce(), _expected_ciphertext(), _aad(), _expected_tag())
expect(_decrypt_ok(res)).to_equal(true)
```

</details>

#### decrypt recovers original plaintext

- decrypt recovers original plaintext
   - Expected: _decrypt_payload(res) equals `_plaintext()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt recovers original plaintext")
val res = chacha20_poly1305_decrypt(_key(), _nonce(), _expected_ciphertext(), _aad(), _expected_tag())
expect(_decrypt_payload(res)).to_equal(_plaintext())
```

</details>

#### decrypt with wrong tag fails authentication

- decrypt with wrong tag fails authentication
   - Expected: _decrypt_ok(res) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt with wrong tag fails authentication")
var bad_tag: [u8] = []
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
val res = chacha20_poly1305_decrypt(_key(), _nonce(), _expected_ciphertext(), _aad(), bad_tag)
expect(_decrypt_ok(res)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/chacha20_poly1305_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ChaCha20-Poly1305 RFC 8439 §2.8.2 AEAD KAT.
- ChaCha20-Poly1305 RFC 8439 §2.8.2 AEAD KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `6d018b1fe58a59fb230a6d86f5adcf39d31bef56177ba7e93fec118cb05422e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d018b1fe58a59fb230a6d86f5adcf39d31bef56177ba7e93fec118cb05422e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d018b1fe58a59fb230a6d86f5adcf39d31bef56177ba7e93fec118cb05422e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/chacha20_poly1305_spec.spl
mirror: doc/06_spec/unit/os/crypto/chacha20_poly1305_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/chacha20_poly1305_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/chacha20_poly1305_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/chacha20_poly1305_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/chacha20_poly1305_spec.spl:431:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypt produces correct total output length (114 ciphertext + 16 tag = 130 bytes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/chacha20_poly1305_spec.spl:437:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypt produces correct ciphertext bytes (first 16)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/chacha20_poly1305_spec.spl:445:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypt produces correct ciphertext bytes (bytes 16-32)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
