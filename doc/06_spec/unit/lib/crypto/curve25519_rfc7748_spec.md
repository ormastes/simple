# Curve25519 Rfc7748 Specification

> Tests covering Curve25519 RFC 7748 §5.2 single scalar-mult test vectors, Curve25519 RFC 7748 §5.2 iterated scalar-mult, Curve25519 RFC 7748 §6.1 ECDH key exchange.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Curve25519 Rfc7748 Specification

## Scenarios

### Curve25519 RFC 7748 §5.2 single scalar-mult test vectors

#### TV1: scalar a546e36b... × u e6db6867... → c3da5537...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TV1: scalar a546e36b... × u e6db6867... → c3da5537...
   - Expected: x25519(SCALAR_TV1, U_TV1) equals `EXPECTED_TV1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TV1: scalar a546e36b... × u e6db6867... → c3da5537...")
expect(x25519(SCALAR_TV1, U_TV1)).to_equal(EXPECTED_TV1)
```

</details>

#### TV2: scalar 4b66e9d4... × u e5210f12... → 95cbde94...

- TV2: scalar 4b66e9d4... × u e5210f12... → 95cbde94...
   - Expected: x25519(SCALAR_TV2, U_TV2) equals `EXPECTED_TV2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TV2: scalar 4b66e9d4... × u e5210f12... → 95cbde94...")
expect(x25519(SCALAR_TV2, U_TV2)).to_equal(EXPECTED_TV2)
```

</details>

### Curve25519 RFC 7748 §5.2 iterated scalar-mult

#### after 1 iteration starting from BASE_POINT: 422c8e7a...

- after 1 iteration starting from BASE_POINT: 422c8e7a...
   - Expected: x25519(BASE_POINT, BASE_POINT) equals `EXPECTED_AFTER_1_ITER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after 1 iteration starting from BASE_POINT: 422c8e7a...")
expect(x25519(BASE_POINT, BASE_POINT)).to_equal(EXPECTED_AFTER_1_ITER)
```

</details>

### Curve25519 RFC 7748 §6.1 ECDH key exchange

#### Alice public key: x25519(alice_priv, base) == alice_pub

- Alice public key: x25519(alice_priv, base) == alice_pub
   - Expected: x25519_base(ALICE_PRIV) equals `ALICE_PUB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice public key: x25519(alice_priv, base) == alice_pub")
expect(x25519_base(ALICE_PRIV)).to_equal(ALICE_PUB)
```

</details>

#### Bob public key: x25519(bob_priv, base) == bob_pub

- Bob public key: x25519(bob_priv, base) == bob_pub
   - Expected: x25519_base(BOB_PRIV) equals `BOB_PUB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bob public key: x25519(bob_priv, base) == bob_pub")
expect(x25519_base(BOB_PRIV)).to_equal(BOB_PUB)
```

</details>

#### Alice computes shared secret: x25519(alice_priv, bob_pub) == shared_secret

- Alice computes shared secret: x25519(alice_priv, bob_pub) == shared_secret
   - Expected: x25519(ALICE_PRIV, BOB_PUB) equals `SHARED_SECRET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Alice computes shared secret: x25519(alice_priv, bob_pub) == shared_secret")
expect(x25519(ALICE_PRIV, BOB_PUB)).to_equal(SHARED_SECRET)
```

</details>

#### Bob computes shared secret: x25519(bob_priv, alice_pub) == shared_secret

- Bob computes shared secret: x25519(bob_priv, alice_pub) == shared_secret
   - Expected: x25519(BOB_PRIV, ALICE_PUB) equals `SHARED_SECRET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bob computes shared secret: x25519(bob_priv, alice_pub) == shared_secret")
expect(x25519(BOB_PRIV, ALICE_PUB)).to_equal(SHARED_SECRET)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/curve25519_rfc7748_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Curve25519 RFC 7748 §5.2 single scalar-mult test vectors, Curve25519 RFC 7748 §5.2 iterated scalar-mult, Curve25519 RFC 7748 §6.1 ECDH key exchange.
- Curve25519 RFC 7748 §5.2 single scalar-mult test vectors
- Curve25519 RFC 7748 §5.2 iterated scalar-mult
- Curve25519 RFC 7748 §6.1 ECDH key exchange

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

- Canonical SPipe generation for source `84bba00497f184be94bce5174993f50140b9b5d05fb606dc872e7226f3e06ff1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84bba00497f184be94bce5174993f50140b9b5d05fb606dc872e7226f3e06ff1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84bba00497f184be94bce5174993f50140b9b5d05fb606dc872e7226f3e06ff1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/curve25519_rfc7748_spec.spl
mirror: doc/06_spec/unit/lib/crypto/curve25519_rfc7748_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/curve25519_rfc7748_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/curve25519_rfc7748_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/curve25519_rfc7748_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TV1: scalar a546e36b... × u e6db6867... → c3da5537...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/curve25519_rfc7748_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TV2: scalar 4b66e9d4... × u e5210f12... → 95cbde94...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/curve25519_rfc7748_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'after 1 iteration starting from BASE_POINT: 422c8e7a...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
