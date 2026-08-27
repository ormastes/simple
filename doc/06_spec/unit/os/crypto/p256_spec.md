# P256 Specification

> Tests covering P-256 ECDSA/ECDH — RFC 6979 known-answer tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Specification

## Scenarios

### P-256 ECDSA/ECDH — RFC 6979 known-answer tests

#### keygen produces 65-byte uncompressed pubkey

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keygen produces 65-byte uncompressed pubkey
   - Expected: pk.len() equals `65`
   - Expected: pk[0u64] equals `0x04u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keygen produces 65-byte uncompressed pubkey")
val sk = _rfc6979_privkey()
val pk = p256_keygen(sk)
expect(pk.len()).to_equal(65)
expect(pk[0u64]).to_equal(0x04u8)
```

</details>

#### generated pubkey is on curve

- generated pubkey is on curve
   - Expected: p256_point_on_curve(px, py) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generated pubkey is on curve")
val sk = _rfc6979_privkey()
val pk = p256_keygen(sk)
val px = _get_pubkey_x(pk)
val py = _get_pubkey_y(pk)
expect(p256_point_on_curve(px, py)).to_equal(true)
```

</details>

#### ECDSA sign produces 64-byte signature

- ECDSA sign produces 64-byte signature
   - Expected: sig.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ECDSA sign produces 64-byte signature")
val sk = _rfc6979_privkey()
val msg = _sample_msg()
val msg_hash = sha256(msg)
val sig = p256_ecdsa_sign(sk, msg_hash)
expect(sig.len()).to_equal(64)
```

</details>

#### ECDSA sign matches RFC 6979 r value

- ECDSA sign matches RFC 6979 r value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ECDSA sign matches RFC 6979 r value")
val sk = _rfc6979_privkey()
val msg = _sample_msg()
val msg_hash = sha256(msg)
val sig = p256_ecdsa_sign(sk, msg_hash)
val r_bytes = _extract_first_32(sig)
expect(_bytes_hex(r_bytes)).to_equal(
    "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716"
)
```

</details>

#### p256_add(1, 1) mod p == 2

- p256_add(1, 1) mod p == 2
   - Expected: _bytes_hex(two_bytes) equals `_bytes_hex(expected)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("p256_add(1, 1) mod p == 2")
val one = _be32_val(0x01u8)
val two_bytes = p256_add(one, one)
val expected = _be32_val(0x02u8)
expect(_bytes_hex(two_bytes)).to_equal(_bytes_hex(expected))
```

</details>

#### p256_mul(2, 3) mod p == 6

- p256_mul(2, 3) mod p == 6
   - Expected: _bytes_hex(six_bytes) equals `_bytes_hex(expected)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("p256_mul(2, 3) mod p == 6")
val two = _be32_val(0x02u8)
val three = _be32_val(0x03u8)
val six_bytes = p256_mul(two, three)
val expected = _be32_val(0x06u8)
expect(_bytes_hex(six_bytes)).to_equal(_bytes_hex(expected))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/p256_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering P-256 ECDSA/ECDH — RFC 6979 known-answer tests.
- P-256 ECDSA/ECDH — RFC 6979 known-answer tests

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

- Canonical SPipe generation for source `bfe1241a7942fa45a158c42543336d3ac602c14e5f21365935fc25ad25efe260`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bfe1241a7942fa45a158c42543336d3ac602c14e5f21365935fc25ad25efe260`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bfe1241a7942fa45a158c42543336d3ac602c14e5f21365935fc25ad25efe260`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/p256_spec.spl
mirror: doc/06_spec/unit/os/crypto/p256_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/p256_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/p256_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/p256_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/p256_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keygen produces 65-byte uncompressed pubkey' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/p256_spec.spl:253:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generated pubkey is on curve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/p256_spec.spl:262:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ECDSA sign produces 64-byte signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
