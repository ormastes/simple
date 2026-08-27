# Fe25519 Specification

> Tests covering Fe25519 — RFC 7748 byte-edge round-trip, Fe25519 — constants, Fe25519 — additive structure, Fe25519 — multiplicative structure, Fe25519 — inversion (Fermat's Little Theorem), Fe25519 — generic exponentiation, Fe25519 — constant-time selectors, Fe25519 — equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fe25519 Specification

## Scenarios

### Fe25519 — RFC 7748 byte-edge round-trip

#### decodes then re-encodes the X25519 base u-coord (u=9)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes then re-encodes the X25519 base u-coord (u=9)
   - Expected: _bytes_eq(out, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes then re-encodes the X25519 base u-coord (u=9)")
val b = _mask_high_bit(_base_u_bytes())
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

#### decodes then re-encodes Alice's RFC 7748 §6.1 private scalar

- decodes then re-encodes Alice's RFC 7748 §6.1 private scalar
   - Expected: _bytes_eq(out, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes then re-encodes Alice's RFC 7748 §6.1 private scalar")
val b = _mask_high_bit(_alice_priv_bytes())
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

#### decodes then re-encodes Bob's RFC 7748 §6.1 private scalar

- decodes then re-encodes Bob's RFC 7748 §6.1 private scalar
   - Expected: _bytes_eq(out, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes then re-encodes Bob's RFC 7748 §6.1 private scalar")
val b = _mask_high_bit(_bob_priv_bytes())
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

### Fe25519 — constants

#### fe_zero encodes to all zero bytes

- fe_zero encodes to all zero bytes
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_zero encodes to all zero bytes")
val out = fe_to_bytes(fe_zero())
var ok = true
var i: u64 = 0
while i < 32:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### fe_one encodes to byte 0x01 followed by 31 zeros

- fe_one encodes to byte 0x01 followed by 31 zeros
   - Expected: out[0] equals `0x01`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_one encodes to byte 0x01 followed by 31 zeros")
val out = fe_to_bytes(fe_one())
expect(out[0]).to_equal(0x01)
var ok = true
var i: u64 = 1
while i < 32:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### fe_is_zero(zero) is true; fe_is_zero(one) is false

- fe_is_zero(zero) is true; fe_is_zero(one) is false
   - Expected: fe_is_zero(fe_zero()) is true
   - Expected: fe_is_zero(fe_one()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_is_zero(zero) is true; fe_is_zero(one) is false")
expect(fe_is_zero(fe_zero())).to_equal(true)
expect(fe_is_zero(fe_one())).to_equal(false)
```

</details>

### Fe25519 — additive structure

#### fe_add(a, fe_zero()) == a

- fe_add(a, fe_zero()) == a
   - Expected: fe_eq(r, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_add(a, fe_zero()) == a")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val r = fe_add(a, fe_zero())
expect(fe_eq(r, a)).to_equal(true)
```

</details>

#### fe_sub(a, a) == fe_zero()

- fe_sub(a, a) == fe_zero()
   - Expected: fe_is_zero(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sub(a, a) == fe_zero()")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val r = fe_sub(a, a)
expect(fe_is_zero(r)).to_equal(true)
```

</details>

#### fe_neg(a) + a == fe_zero()

- fe_neg(a) + a == fe_zero()
   - Expected: fe_is_zero(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_neg(a) + a == fe_zero()")
val a = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_add(fe_neg(a), a)
expect(fe_is_zero(r)).to_equal(true)
```

</details>

### Fe25519 — multiplicative structure

#### fe_mul is commutative

- fe_mul is commutative
   - Expected: fe_eq(ab, ba) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul is commutative")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val ab = fe_mul(a, b)
val ba = fe_mul(b, a)
expect(fe_eq(ab, ba)).to_equal(true)
```

</details>

#### fe_mul(x, fe_one()) == x

- fe_mul(x, fe_one()) == x
   - Expected: fe_eq(r, x) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(x, fe_one()) == x")
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val r = fe_mul(x, fe_one())
expect(fe_eq(r, x)).to_equal(true)
```

</details>

#### fe_mul(x, fe_zero()) == fe_zero()

- fe_mul(x, fe_zero()) == fe_zero()
   - Expected: fe_is_zero(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_mul(x, fe_zero()) == fe_zero()")
val x = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_mul(x, fe_zero())
expect(fe_is_zero(r)).to_equal(true)
```

</details>

#### fe_sq(x) == fe_mul(x, x)

- fe_sq(x) == fe_mul(x, x)
   - Expected: fe_eq(s1, s2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_sq(x) == fe_mul(x, x)")
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val s1 = fe_sq(x)
val s2 = fe_mul(x, x)
expect(fe_eq(s1, s2)).to_equal(true)
```

</details>

### Fe25519 — inversion (Fermat's Little Theorem)

#### fe_invert(x) * x == fe_one() for the X25519 base u

- fe_invert(x) * x == fe_one() for the X25519 base u
   - Expected: fe_eq(r, fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_invert(x) * x == fe_one() for the X25519 base u")
val x = fe_from_bytes(_mask_high_bit(_base_u_bytes()))
val xi = fe_invert(x)
val r = fe_mul(xi, x)
expect(fe_eq(r, fe_one())).to_equal(true)
```

</details>

#### fe_invert(x) * x == fe_one() for Alice's scalar

- fe_invert(x) * x == fe_one() for Alice's scalar
   - Expected: fe_eq(r, fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_invert(x) * x == fe_one() for Alice's scalar")
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val xi = fe_inv(x)
val r = fe_mul(xi, x)
expect(fe_eq(r, fe_one())).to_equal(true)
```

</details>

#### fe_invert(x) * x == fe_one() for Bob's scalar

- fe_invert(x) * x == fe_one() for Bob's scalar
   - Expected: fe_eq(r, fe_one()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_invert(x) * x == fe_one() for Bob's scalar")
val x = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val xi = fe_invert(x)
val r = fe_mul(xi, x)
expect(fe_eq(r, fe_one())).to_equal(true)
```

</details>

### Fe25519 — generic exponentiation

#### fe_pow(x, [2]) equals fe_sq(x)

- fe_pow(x, [2]) equals fe_sq(x)
   - Expected: fe_eq(r, s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_pow(x, [2]) equals fe_sq(x)")
val x = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val pow_e = [0x02.to_u8()]
val r = fe_pow(x, pow_e)
val s = fe_sq(x)
expect(fe_eq(r, s)).to_equal(true)
```

</details>

#### fe_pow(x, [1]) equals x

- fe_pow(x, [1]) equals x
   - Expected: fe_eq(r, x) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_pow(x, [1]) equals x")
val x = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val pow_e = [0x01.to_u8()]
val r = fe_pow(x, pow_e)
expect(fe_eq(r, x)).to_equal(true)
```

</details>

### Fe25519 — constant-time selectors

#### fe_cond_select(a, b, 0) == a

- fe_cond_select(a, b, 0) == a
   - Expected: fe_eq(r, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_select(a, b, 0) == a")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_cond_select(a, b, 0)
expect(fe_eq(r, a)).to_equal(true)
```

</details>

#### fe_cond_select(a, b, 1) == b

- fe_cond_select(a, b, 1) == b
   - Expected: fe_eq(r, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_select(a, b, 1) == b")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val r = fe_cond_select(a, b, 1)
expect(fe_eq(r, b)).to_equal(true)
```

</details>

#### fe_cond_swap with swap=1 is fe_cond_swap with swap=0 reversed

- fe_cond_swap with swap=1 is fe_cond_swap with swap=0 reversed
   - Expected: fe_eq(a0, a) is true
   - Expected: fe_eq(b0, b) is true
   - Expected: fe_eq(a1, b) is true
   - Expected: fe_eq(b1, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_cond_swap with swap=1 is fe_cond_swap with swap=0 reversed")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
val (a0, b0) = fe_cond_swap(a, b, 0)
val (a1, b1) = fe_cond_swap(a, b, 1)
expect(fe_eq(a0, a)).to_equal(true)
expect(fe_eq(b0, b)).to_equal(true)
expect(fe_eq(a1, b)).to_equal(true)
expect(fe_eq(b1, a)).to_equal(true)
```

</details>

### Fe25519 — equality

#### fe_eq is reflexive

- fe_eq is reflexive
   - Expected: fe_eq(a, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_eq is reflexive")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
expect(fe_eq(a, a)).to_equal(true)
```

</details>

#### fe_eq returns false for distinct inputs

- fe_eq returns false for distinct inputs
   - Expected: fe_eq(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_eq returns false for distinct inputs")
val a = fe_from_bytes(_mask_high_bit(_alice_priv_bytes()))
val b = fe_from_bytes(_mask_high_bit(_bob_priv_bytes()))
expect(fe_eq(a, b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/math/field/fe25519_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Fe25519 — RFC 7748 byte-edge round-trip, Fe25519 — constants, Fe25519 — additive structure, Fe25519 — multiplicative structure, Fe25519 — inversion (Fermat's Little Theorem), Fe25519 — generic exponentiation, Fe25519 — constant-time selectors, Fe25519 — equality.
- Fe25519 — RFC 7748 byte-edge round-trip
- Fe25519 — constants
- Fe25519 — additive structure
- Fe25519 — multiplicative structure
- Fe25519 — inversion (Fermat's Little Theorem)
- Fe25519 — generic exponentiation
- Fe25519 — constant-time selectors
- Fe25519 — equality

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `282c3f19731da6209163c43877468719d6bc5c425f6081036b993d414db4eb90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `282c3f19731da6209163c43877468719d6bc5c425f6081036b993d414db4eb90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `282c3f19731da6209163c43877468719d6bc5c425f6081036b993d414db4eb90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/math/field/fe25519_spec.spl
mirror: doc/06_spec/unit/lib/math/field/fe25519_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/math/field/fe25519_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/math/field/fe25519_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/math/field/fe25519_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes then re-encodes the X25519 base u-coord (u=9)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/field/fe25519_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes then re-encodes Alice's RFC 7748 §6.1 private scalar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/field/fe25519_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes then re-encodes Bob's RFC 7748 §6.1 private scalar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
