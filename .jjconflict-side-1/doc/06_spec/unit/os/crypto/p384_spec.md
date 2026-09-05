# P384 Specification

> Tests covering P-384.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P384 Specification

## Scenarios

### P-384

#### field add and mul

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- field add and mul
   - Expected: _bytes_hex(two_bytes) equals `_bytes_hex(two)`
   - Expected: _bytes_hex(six_bytes) equals `_bytes_hex(six)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("field add and mul")
val one = _be48_val(0x01)
val two_bytes = p384_add(one, one)
val two = _be48_val(0x02)
expect(_bytes_hex(two_bytes)).to_equal(_bytes_hex(two))
val three = _be48_val(0x03)
val six_bytes = p384_mul(two, three)
val six = _be48_val(0x06)
expect(_bytes_hex(six_bytes)).to_equal(_bytes_hex(six))
```

</details>

#### Generator G is on the P-384 curve

- Generator G is on the P-384 curve
   - Expected: p384_point_on_curve(_gx_bytes(), _gy_bytes()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Generator G is on the P-384 curve")
expect(p384_point_on_curve(_gx_bytes(), _gy_bytes())).to_equal(true)
```

</details>

#### scalar multiplication matches exact public-key KAT for k=1

- scalar multiplication matches exact public-key KAT for k=1
   - Expected: _bytes_hex(k1_pub) equals `_pub_hex_k1()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar multiplication matches exact public-key KAT for k=1")
val k1_pub = p384_scalar_mult(_be48_val(0x01), _gx_bytes(), _gy_bytes())
expect(_bytes_hex(k1_pub)).to_equal(_pub_hex_k1())
```

</details>

#### scalar multiplication matches exact public-key KAT for k=2

- scalar multiplication matches exact public-key KAT for k=2
   - Expected: _bytes_hex(k2_pub) equals `_pub_hex_k2()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar multiplication matches exact public-key KAT for k=2")
val k2_pub = p384_scalar_mult(_be48_val(0x02), _gx_bytes(), _gy_bytes())
expect(_bytes_hex(k2_pub)).to_equal(_pub_hex_k2())
```

</details>

#### scalar multiplication matches exact public-key KAT for k=3

- scalar multiplication matches exact public-key KAT for k=3
   - Expected: _bytes_hex(k3_pub) equals `_pub_hex_k3()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar multiplication matches exact public-key KAT for k=3")
val k3_pub = p384_scalar_mult(_be48_val(0x03), _gx_bytes(), _gy_bytes())
expect(_bytes_hex(k3_pub)).to_equal(_pub_hex_k3())
```

</details>

#### keygen matches exact public-key KAT for seeded private key 0x6B

- keygen matches exact public-key KAT for seeded private key 0x6B
   - Expected: _bytes_hex(p384_keygen(_make_key(0x6B))) equals `_pub_hex_alice()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keygen matches exact public-key KAT for seeded private key 0x6B")
expect(_bytes_hex(p384_keygen(_make_key(0x6B)))).to_equal(_pub_hex_alice())
```

</details>

#### keygen matches exact public-key KAT for seeded private key 0x01

- keygen matches exact public-key KAT for seeded private key 0x01
   - Expected: _bytes_hex(p384_keygen(_make_key(0x01))) equals `_pub_hex_bob()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keygen matches exact public-key KAT for seeded private key 0x01")
expect(_bytes_hex(p384_keygen(_make_key(0x01)))).to_equal(_pub_hex_bob())
```

</details>

#### keygen and ECDSA sign-verify round trip

- keygen and ECDSA sign-verify round trip
   - Expected: pub_key.len() equals `97`
   - Expected: pub_key[0u64] equals `0x04u8`
   - Expected: sig.len() equals `96`
   - Expected: p384_ecdsa_verify(pub_key, msg_hash, sig) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keygen and ECDSA sign-verify round trip")
val sk = _make_key(0x6B)
val pub_key = p384_keygen(sk)
expect(pub_key.len()).to_equal(97)
expect(pub_key[0u64]).to_equal(0x04u8)
val msg_hash = sha384(_make_key(0x01))
val sig = p384_ecdsa_sign(sk, msg_hash)
expect(sig.len()).to_equal(96)
expect(p384_ecdsa_verify(pub_key, msg_hash, sig)).to_equal(true)
```

</details>

#### ECDH commutativity

- ECDH commutativity
   - Expected: _bytes_hex(shared_ab) equals `_bytes_hex(shared_ba)`
   - Expected: _bytes_hex(shared_ab) equals `_shared_hex_alice_bob()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ECDH commutativity")
val alice_priv = _make_key(0x6B)
val bob_priv = _make_key(0x01)
val alice_pub = p384_keygen(alice_priv)
val bob_pub = p384_keygen(bob_priv)
val shared_ab = p384_ecdh(alice_priv, bob_pub)
val shared_ba = p384_ecdh(bob_priv, alice_pub)
expect(_bytes_hex(shared_ab)).to_equal(_bytes_hex(shared_ba))
expect(_bytes_hex(shared_ab)).to_equal(_shared_hex_alice_bob())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/p384_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering P-384.
- P-384

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

- Canonical SPipe generation for source `290a78d898d18b703b98983c0c30f22f0000cda0b6bf641c01f32b590a6a20b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `290a78d898d18b703b98983c0c30f22f0000cda0b6bf641c01f32b590a6a20b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `290a78d898d18b703b98983c0c30f22f0000cda0b6bf641c01f32b590a6a20b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/p384_spec.spl
mirror: doc/06_spec/unit/os/crypto/p384_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/p384_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/p384_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/p384_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/p384_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'field add and mul' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/p384_spec.spl:202:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Generator G is on the P-384 curve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/p384_spec.spl:207:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scalar multiplication matches exact public-key KAT for k=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
