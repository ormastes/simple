# Ffdhe Kat Specification

> Tests covering FFDHE RFC 7919 — §1 small-prime DH sanity (p=23, g=2), FFDHE RFC 7919 — §2 ffdhe2048 prime integrity, FFDHE RFC 7919 — §3 ffdhe3072 prime integrity, FFDHE RFC 7919 — §4 ffdhe4096 prime integrity, FFDHE RFC 7919 — §5 ffdhe2048 Alice/Bob round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffdhe Kat Specification

## Scenarios

### FFDHE RFC 7919 — §1 small-prime DH sanity (p=23, g=2)

#### Alice pub = g^4 mod 23 = 16

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Alice pub = g^4 mod 23 = 16
   - Expected: pub_bytes[0].to_i64() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice pub = g^4 mod 23 = 16")
val p = _small_p()
val g = _small_g()
val kp = ffdhe_keygen(p, g, _alice_scalar())
val pub_bytes = ffdhe_pub_to_bytes(kp[1], 1)
expect(pub_bytes[0].to_i64()).to_equal(16)
```

</details>

#### Bob pub = g^7 mod 23 = 13

- Bob pub = g^7 mod 23 = 13
   - Expected: pub_bytes[0].to_i64() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bob pub = g^7 mod 23 = 13")
val p = _small_p()
val g = _small_g()
val kp = ffdhe_keygen(p, g, _bob_scalar())
val pub_bytes = ffdhe_pub_to_bytes(kp[1], 1)
expect(pub_bytes[0].to_i64()).to_equal(13)
```

</details>

#### Alice and Bob derive the same shared secret (18)

- Alice and Bob derive the same shared secret (18)
   - Expected: sa_bytes[0].to_i64() equals `18`
   - Expected: sb_bytes[0].to_i64() equals `18`
   - Expected: sa_bytes[0] equals `sb_bytes[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice and Bob derive the same shared secret (18)")
val p = _small_p()
val g = _small_g()
val alice_kp = ffdhe_keygen(p, g, _alice_scalar())
val bob_kp   = ffdhe_keygen(p, g, _bob_scalar())
val shared_alice = ffdhe_dh(alice_kp[0], bob_kp[1], p)
val shared_bob   = ffdhe_dh(bob_kp[0], alice_kp[1], p)
val sa_bytes = ffdhe_pub_to_bytes(shared_alice, 1)
val sb_bytes = ffdhe_pub_to_bytes(shared_bob, 1)
expect(sa_bytes[0].to_i64()).to_equal(18)
expect(sb_bytes[0].to_i64()).to_equal(18)
expect(sa_bytes[0]).to_equal(sb_bytes[0])
```

</details>

#### round-trip byte serialization of small pub key

- round-trip byte serialization of small pub key
   - Expected: recovered_bytes[0] equals `pub_bytes[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip byte serialization of small pub key")
val p = _small_p()
val g = _small_g()
val kp = ffdhe_keygen(p, g, _alice_scalar())
val pub_bytes = ffdhe_pub_to_bytes(kp[1], 1)
val recovered = ffdhe_bytes_to_pub(pub_bytes)
val recovered_bytes = ffdhe_pub_to_bytes(recovered, 1)
expect(recovered_bytes[0]).to_equal(pub_bytes[0])
```

</details>

### FFDHE RFC 7919 — §2 ffdhe2048 prime integrity

#### ffdhe2048_p() encodes to exactly 256 bytes

- ffdhe2048_p() encodes to exactly 256 bytes
   - Expected: pb.len().to_i64() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe2048_p() encodes to exactly 256 bytes")
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
expect(pb.len().to_i64()).to_equal(256)
```

</details>

#### ffdhe2048 SHA-256 fingerprint matches RFC 7919 Appendix A.1

- ffdhe2048 SHA-256 fingerprint matches RFC 7919 Appendix A.1


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe2048 SHA-256 fingerprint matches RFC 7919 Appendix A.1")
# Computed: python3 -c \"import hashlib; print(hashlib.sha256(bytes.fromhex(hex)).hexdigest())\"
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
val fp = _bytes_to_hex(sha256(pb))
expect(fp).to_equal(
    "d417dfe49b439655f30febdda2200fec593724fd78029662be911a1bcfd701da"
)
```

</details>

#### ffdhe2048 first byte is 0xFF

- ffdhe2048 first byte is 0xFF
   - Expected: pb[0].to_i64() equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe2048 first byte is 0xFF")
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
expect(pb[0].to_i64()).to_equal(255)
```

</details>

#### ffdhe2048 last byte is 0xFF

- ffdhe2048 last byte is 0xFF
   - Expected: pb[255].to_i64() equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe2048 last byte is 0xFF")
val p = ffdhe2048_p()
val pb = ffdhe_prime_bytes(p, 256)
expect(pb[255].to_i64()).to_equal(255)
```

</details>

### FFDHE RFC 7919 — §3 ffdhe3072 prime integrity

#### ffdhe3072_p() encodes to exactly 384 bytes

- ffdhe3072_p() encodes to exactly 384 bytes
   - Expected: pb.len().to_i64() equals `384`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe3072_p() encodes to exactly 384 bytes")
val p = ffdhe3072_p()
val pb = ffdhe_prime_bytes(p, 384)
expect(pb.len().to_i64()).to_equal(384)
```

</details>

#### ffdhe3072 SHA-256 fingerprint matches RFC 7919 Appendix A.2

- ffdhe3072 SHA-256 fingerprint matches RFC 7919 Appendix A.2


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe3072 SHA-256 fingerprint matches RFC 7919 Appendix A.2")
val p = ffdhe3072_p()
val pb = ffdhe_prime_bytes(p, 384)
val fp = _bytes_to_hex(sha256(pb))
expect(fp).to_equal(
    "0eaf67db3a839156d5013494a5318a772b5697d270d721f37f092efc69ea5a17"
)
```

</details>

### FFDHE RFC 7919 — §4 ffdhe4096 prime integrity

#### ffdhe4096_p() encodes to exactly 512 bytes

- ffdhe4096_p() encodes to exactly 512 bytes
   - Expected: pb.len().to_i64() equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe4096_p() encodes to exactly 512 bytes")
val p = ffdhe4096_p()
val pb = ffdhe_prime_bytes(p, 512)
expect(pb.len().to_i64()).to_equal(512)
```

</details>

#### ffdhe4096 SHA-256 fingerprint matches RFC 7919 Appendix A.3

- ffdhe4096 SHA-256 fingerprint matches RFC 7919 Appendix A.3


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ffdhe4096 SHA-256 fingerprint matches RFC 7919 Appendix A.3")
val p = ffdhe4096_p()
val pb = ffdhe_prime_bytes(p, 512)
val fp = _bytes_to_hex(sha256(pb))
expect(fp).to_equal(
    "4648414224ac881b3d0dc59b466f96d06a558278776807797ecf1f66ff397b3e"
)
```

</details>

### FFDHE RFC 7919 — §5 ffdhe2048 Alice/Bob round-trip

#### Alice and Bob derive the same 256-byte shared secret

- Alice and Bob derive the same 256-byte shared secret


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice and Bob derive the same 256-byte shared secret")
pending("2048-bit modexp is O(minutes) in interpreter; deferred to native rt_modexp (see doc/02_requirements/feature/ffdhe_native_modexp_2026-05-02.md)")
```

</details>

#### Alice public key is in range (1 < pub < p-1)

- Alice public key is in range (1 < pub < p-1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice public key is in range (1 < pub < p-1)")
pending("2048-bit modexp is O(minutes) in interpreter; deferred to native rt_modexp (see doc/02_requirements/feature/ffdhe_native_modexp_2026-05-02.md)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/ffdhe_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FFDHE RFC 7919 — §1 small-prime DH sanity (p=23, g=2), FFDHE RFC 7919 — §2 ffdhe2048 prime integrity, FFDHE RFC 7919 — §3 ffdhe3072 prime integrity, FFDHE RFC 7919 — §4 ffdhe4096 prime integrity, FFDHE RFC 7919 — §5 ffdhe2048 Alice/Bob round-trip.
- FFDHE RFC 7919 — §1 small-prime DH sanity (p=23, g=2)
- FFDHE RFC 7919 — §2 ffdhe2048 prime integrity
- FFDHE RFC 7919 — §3 ffdhe3072 prime integrity
- FFDHE RFC 7919 — §4 ffdhe4096 prime integrity
- FFDHE RFC 7919 — §5 ffdhe2048 Alice/Bob round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `9f575ef45be631bb755e6d8f0998bfd88b6eafb417489b86684f824cbbc94d89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f575ef45be631bb755e6d8f0998bfd88b6eafb417489b86684f824cbbc94d89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f575ef45be631bb755e6d8f0998bfd88b6eafb417489b86684f824cbbc94d89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/crypto/ffdhe_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/ffdhe_kat_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/unit/os/crypto/ffdhe_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/ffdhe_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/ffdhe_kat_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/os/crypto/ffdhe_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/ffdhe_kat_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Alice pub = g^4 mod 23 = 16' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/ffdhe_kat_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Bob pub = g^7 mod 23 = 13' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/ffdhe_kat_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Alice and Bob derive the same shared secret (18)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
