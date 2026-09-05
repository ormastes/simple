# Rsa Pss Sha256 Roundtrip Slow Specification

> Tests covering RSA-PSS-SHA-256 sign + verify round-trip (RSA-2048, slow).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Pss Sha256 Roundtrip Slow Specification

## Scenarios

### RSA-PSS-SHA-256 sign + verify round-trip (RSA-2048, slow)

#### produces 256-byte signature for RSA-2048 key (sLen=0)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces 256-byte signature for RSA-2048 key (sLen=0)
   - Expected: sig.len().to_i64() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces 256-byte signature for RSA-2048 key (sLen=0)")
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
expect(sig.len().to_i64()).to_equal(256)
```

</details>

#### verifies signature with sLen=0 (deterministic encoding)

- verifies signature with sLen=0 (deterministic encoding)
   - Expected: rsa_pss_sha256_verify_with_slen(_spki(), _msg_hello(), sig, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies signature with sLen=0 (deterministic encoding)")
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
expect(rsa_pss_sha256_verify_with_slen(_spki(), _msg_hello(), sig, 0)).to_equal(true)
```

</details>

#### verifies signature with sLen=32 (default hLen)

- verifies signature with sLen=32 (default hLen)
   - Expected: rsa_pss_sha256_verify(_spki(), _msg_hello(), sig) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies signature with sLen=32 (default hLen)")
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _fixed_salt_32())
expect(rsa_pss_sha256_verify(_spki(), _msg_hello(), sig)).to_equal(true)
```

</details>

#### deterministic PSS (sLen=0) is byte-reproducible

- deterministic PSS (sLen=0) is byte-reproducible
   - Expected: s1.len().to_i64() equals `s2.len().to_i64()`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deterministic PSS (sLen=0) is byte-reproducible")
val s1 = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
val s2 = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
expect(s1.len().to_i64()).to_equal(s2.len().to_i64())
var i: u64 = 0
var ok: bool = true
while i < s1.len():
    if s1[i] != s2[i]:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### rejects signature with last byte flipped

- rejects signature with last byte flipped
   - Expected: rsa_pss_sha256_verify(_spki(), _msg_hello(), tampered) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects signature with last byte flipped")
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _fixed_salt_32())
val tampered = _flip_byte(sig, sig.len() - 1u64)
expect(rsa_pss_sha256_verify(_spki(), _msg_hello(), tampered)).to_equal(false)
```

</details>

#### rejects valid signature against different message

- rejects valid signature against different message
   - Expected: rsa_pss_sha256_verify(_spki(), _msg_different(), sig) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects valid signature against different message")
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _fixed_salt_32())
expect(rsa_pss_sha256_verify(_spki(), _msg_different(), sig)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RSA-PSS-SHA-256 sign + verify round-trip (RSA-2048, slow).
- RSA-PSS-SHA-256 sign + verify round-trip (RSA-2048, slow)

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

- Canonical SPipe generation for source `331cedfdb661b13cfc0070cbc4726be4f3855fc994178dd6e110914108f27d43`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `331cedfdb661b13cfc0070cbc4726be4f3855fc994178dd6e110914108f27d43`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `331cedfdb661b13cfc0070cbc4726be4f3855fc994178dd6e110914108f27d43`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl
mirror: doc/06_spec/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces 256-byte signature for RSA-2048 key (sLen=0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies signature with sLen=0 (deterministic encoding)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies signature with sLen=32 (default hLen)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
