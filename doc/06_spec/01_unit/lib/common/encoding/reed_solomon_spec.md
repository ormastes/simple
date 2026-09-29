# Reed Solomon Specification

> Tests covering GF(2^8) arithmetic, RS encode, RS decode (erasure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reed Solomon Specification

## Scenarios

### GF(2^8) arithmetic

#### addition is XOR

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- addition is XOR
   - Expected: _gf_add_basic() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("addition is XOR")
expect(_gf_add_basic()).to_equal(true)
```

</details>

#### a + a = 0 (self-inverse)

- a + a = 0 (self-inverse)
   - Expected: _gf_add_self_zero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a + a = 0 (self-inverse)")
expect(_gf_add_self_zero()).to_equal(true)
```

</details>

#### multiplication by 1 is identity

- multiplication by 1 is identity
   - Expected: _gf_mul_identity() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiplication by 1 is identity")
expect(_gf_mul_identity()).to_equal(true)
```

</details>

#### multiplication by 0 is zero

- multiplication by 0 is zero
   - Expected: _gf_mul_zero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiplication by 0 is zero")
expect(_gf_mul_zero()).to_equal(true)
```

</details>

#### multiplication is commutative

- multiplication is commutative
   - Expected: _gf_mul_commutativity() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiplication is commutative")
expect(_gf_mul_commutativity()).to_equal(true)
```

</details>

#### 2 * 2 = 4 (no reduction)

- 2 * 2 = 4 (no reduction)
   - Expected: _gf_mul_known_value() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2 * 2 = 4 (no reduction)")
expect(_gf_mul_known_value()).to_equal(true)
```

</details>

#### 0x80 * 2 = 0x1D (with reduction)

- 0x80 * 2 = 0x1D (with reduction)
   - Expected: _gf_mul_with_reduction() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0x80 * 2 = 0x1D (with reduction)")
expect(_gf_mul_with_reduction()).to_equal(true)
```

</details>

#### a * inv(a) = 1

- a * inv(a) = 1
   - Expected: _gf_inv_basic() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a * inv(a) = 1")
expect(_gf_inv_basic()).to_equal(true)
```

</details>

#### inv(1) = 1

- inv(1) = 1
   - Expected: _gf_inv_one() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inv(1) = 1")
expect(_gf_inv_one()).to_equal(true)
```

</details>

#### all non-zero elements have valid inverses

- all non-zero elements have valid inverses
   - Expected: _gf_inv_all_nonzero() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all non-zero elements have valid inverses")
expect(_gf_inv_all_nonzero()).to_equal(true)
```

</details>

#### pow basics: a^0=1, a^1=a

- pow basics: a^0=1, a^1=a
   - Expected: _gf_pow_basic() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow basics: a^0=1, a^1=a")
expect(_gf_pow_basic()).to_equal(true)
```

</details>

#### 2^8 = 0x1D (polynomial reduction)

- 2^8 = 0x1D (polynomial reduction)
   - Expected: _gf_pow_two_cubed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2^8 = 0x1D (polynomial reduction)")
expect(_gf_pow_two_cubed()).to_equal(true)
```

</details>

#### alpha=2 has order 255

- alpha=2 has order 255
   - Expected: _gf_pow_order() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alpha=2 has order 255")
expect(_gf_pow_order()).to_equal(true)
```

</details>

### RS encode

#### output length is data + parity

- output length is data + parity
   - Expected: _enc_basic_no_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output length is data + parity")
expect(_enc_basic_no_error()).to_equal(true)
```

</details>

#### encoding is systematic (data bytes preserved)

- encoding is systematic (data bytes preserved)
   - Expected: _enc_systematic() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encoding is systematic (data bytes preserved)")
expect(_enc_systematic()).to_equal(true)
```

</details>

#### moderate size encoding produces correct length

- moderate size encoding produces correct length
   - Expected: _enc_moderate_size() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moderate size encoding produces correct length")
expect(_enc_moderate_size()).to_equal(true)
```

</details>

#### 256+ total symbols returns error

- 256+ total symbols returns error
   - Expected: _enc_exceeds_field() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("256+ total symbols returns error")
expect(_enc_exceeds_field()).to_equal(true)
```

</details>

### RS decode (erasure)

#### no erasures recovers original data

- no erasures recovers original data
   - Expected: _dec_no_erasures() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no erasures recovers original data")
expect(_dec_no_erasures()).to_equal(true)
```

</details>

#### single data erasure recovered

- single data erasure recovered
   - Expected: _dec_single_data_erasure() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single data erasure recovered")
expect(_dec_single_data_erasure()).to_equal(true)
```

</details>

#### single parity erasure recovered

- single parity erasure recovered
   - Expected: _dec_single_parity_erasure() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single parity erasure recovered")
expect(_dec_single_parity_erasure()).to_equal(true)
```

</details>

#### maximum erasures (= parity count) recovered

- maximum erasures (= parity count) recovered
   - Expected: _dec_max_erasures() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maximum erasures (= parity count) recovered")
expect(_dec_max_erasures()).to_equal(true)
```

</details>

#### too many erasures returns error

- too many erasures returns error
   - Expected: _dec_too_many_erasures() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("too many erasures returns error")
expect(_dec_too_many_erasures()).to_equal(true)
```

</details>

#### larger block (16 data, 4 parity, 4 erasures) round-trips

- larger block (16 data, 4 parity, 4 erasures) round-trips
   - Expected: _dec_roundtrip_larger() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("larger block (16 data, 4 parity, 4 erasures) round-trips")
expect(_dec_roundtrip_larger()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/reed_solomon_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GF(2^8) arithmetic, RS encode, RS decode (erasure).
- GF(2^8) arithmetic
- RS encode
- RS decode (erasure)

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

- Canonical SPipe generation for source `22e1492f5e10cc488558e13fef06521a89e7d4b0c1128c037c53e945ac49cb3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22e1492f5e10cc488558e13fef06521a89e7d4b0c1128c037c53e945ac49cb3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22e1492f5e10cc488558e13fef06521a89e7d4b0c1128c037c53e945ac49cb3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/reed_solomon_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/reed_solomon_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/reed_solomon_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/reed_solomon_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/reed_solomon_spec.spl:326:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'addition is XOR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/reed_solomon_spec.spl:331:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a + a = 0 (self-inverse)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/reed_solomon_spec.spl:336:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiplication by 1 is identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
