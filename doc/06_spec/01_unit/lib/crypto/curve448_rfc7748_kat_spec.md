# Curve448 Rfc7748 Kat Specification

> Tests covering Curve448 RFC 7748 §5.2 single scalar-mult test vectors, Curve448 RFC 7748 §5.2 iterated scalar-mult (1 iteration), Curve448 RFC 7748 §6.2 ECDH key exchange.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Curve448 Rfc7748 Kat Specification

## Scenarios

### Curve448 RFC 7748 §5.2 single scalar-mult test vectors

#### TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...
   - Expected: x448_scalar_mult(SCALAR_TV1, U_TV1) equals `EXPECTED_TV1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...")
expect(x448_scalar_mult(SCALAR_TV1, U_TV1)).to_equal(EXPECTED_TV1)
```

</details>

#### TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...

- TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...
   - Expected: x448_scalar_mult(SCALAR_TV2, U_TV2) equals `EXPECTED_TV2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...")
expect(x448_scalar_mult(SCALAR_TV2, U_TV2)).to_equal(EXPECTED_TV2)
```

</details>

### Curve448 RFC 7748 §5.2 iterated scalar-mult (1 iteration)

#### after 1 iteration from BASE_POINT: 3f482c8a...

- after 1 iteration from BASE_POINT: 3f482c8a...
   - Expected: x448_scalar_mult(BASE_POINT_448, BASE_POINT_448) equals `EXPECTED_ITER1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after 1 iteration from BASE_POINT: 3f482c8a...")
expect(x448_scalar_mult(BASE_POINT_448, BASE_POINT_448)).to_equal(EXPECTED_ITER1)
```

</details>

### Curve448 RFC 7748 §6.2 ECDH key exchange

#### Alice public key: x448_keygen(alice_priv)[1] == alice_pub

- Alice public key: x448_keygen(alice_priv)[1] == alice_pub
   - Expected: kp[1] equals `ALICE_PUB_448`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice public key: x448_keygen(alice_priv)[1] == alice_pub")
val kp = x448_keygen(ALICE_PRIV_448)
expect(kp[1]).to_equal(ALICE_PUB_448)
```

</details>

#### Bob public key: x448_keygen(bob_priv)[1] == bob_pub

- Bob public key: x448_keygen(bob_priv)[1] == bob_pub
   - Expected: kp[1] equals `BOB_PUB_448`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bob public key: x448_keygen(bob_priv)[1] == bob_pub")
val kp = x448_keygen(BOB_PRIV_448)
expect(kp[1]).to_equal(BOB_PUB_448)
```

</details>

#### Alice computes shared secret: x448_dh(alice_priv, bob_pub) == shared

- Alice computes shared secret: x448_dh(alice_priv, bob_pub) == shared
   - Expected: x448_dh(ALICE_PRIV_448, BOB_PUB_448) equals `SHARED_SECRET_448`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice computes shared secret: x448_dh(alice_priv, bob_pub) == shared")
expect(x448_dh(ALICE_PRIV_448, BOB_PUB_448)).to_equal(SHARED_SECRET_448)
```

</details>

#### Bob computes shared secret: x448_dh(bob_priv, alice_pub) == shared

- Bob computes shared secret: x448_dh(bob_priv, alice_pub) == shared
   - Expected: x448_dh(BOB_PRIV_448, ALICE_PUB_448) equals `SHARED_SECRET_448`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bob computes shared secret: x448_dh(bob_priv, alice_pub) == shared")
expect(x448_dh(BOB_PRIV_448, ALICE_PUB_448)).to_equal(SHARED_SECRET_448)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Curve448 RFC 7748 §5.2 single scalar-mult test vectors, Curve448 RFC 7748 §5.2 iterated scalar-mult (1 iteration), Curve448 RFC 7748 §6.2 ECDH key exchange.
- Curve448 RFC 7748 §5.2 single scalar-mult test vectors
- Curve448 RFC 7748 §5.2 iterated scalar-mult (1 iteration)
- Curve448 RFC 7748 §6.2 ECDH key exchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `69ed06d00e8b894a329ed680f21a86b4eef70b99764aea086ce54a43effbe6af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `69ed06d00e8b894a329ed680f21a86b4eef70b99764aea086ce54a43effbe6af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `69ed06d00e8b894a329ed680f21a86b4eef70b99764aea086ce54a43effbe6af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/curve448_rfc7748_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/curve448_rfc7748_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/curve448_rfc7748_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'after 1 iteration from BASE_POINT: 3f482c8a...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
