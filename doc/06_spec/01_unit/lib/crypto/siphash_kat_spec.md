# Siphash Kat Specification

> Tests covering SipHash-2-4 reference vectors (Aumasson & Bernstein 2012), SipHash-1-3 reference vectors (siphasher crate).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Siphash Kat Specification

## Scenarios

### SipHash-2-4 reference vectors (Aumasson & Bernstein 2012)

#### N=0 empty message → 726fdb47dd0e0e31

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- N=0 empty message → 726fdb47dd0e0e31
   - Expected: _u64_to_hex(siphash24(_std_key(), _msg(0))) equals `726fdb47dd0e0e31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=0 empty message → 726fdb47dd0e0e31")
# vecs[0] = {0x31,0x0e,0x0e,0xdd,0x47,0xdb,0x6f,0x72} LE → 0x726fdb47dd0e0e31
expect(_u64_to_hex(siphash24(_std_key(), _msg(0)))).to_equal("726fdb47dd0e0e31")
```

</details>

#### N=8 one full block → 93f5f5799a932462

- N=8 one full block → 93f5f5799a932462
   - Expected: _u64_to_hex(siphash24(_std_key(), _msg(8))) equals `93f5f5799a932462`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=8 one full block → 93f5f5799a932462")
# vecs[8] = {0x62,0x24,0x93,0x9a,0x79,0xf5,0xf5,0x93} LE → 0x93f5f5799a932462
expect(_u64_to_hex(siphash24(_std_key(), _msg(8)))).to_equal("93f5f5799a932462")
```

</details>

#### N=15 one block + 7-byte tail → a129ca6149be45e5

- N=15 one block + 7-byte tail → a129ca6149be45e5
   - Expected: _u64_to_hex(siphash24(_std_key(), _msg(15))) equals `a129ca6149be45e5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=15 one block + 7-byte tail → a129ca6149be45e5")
# vecs[15] = {0xe5,0x45,0xbe,0x49,0x61,0xca,0x29,0xa1} LE → 0xa129ca6149be45e5
expect(_u64_to_hex(siphash24(_std_key(), _msg(15)))).to_equal("a129ca6149be45e5")
```

</details>

#### N=60 multi-block 4-byte tail → 6ca4ecb15c5f91e1

- N=60 multi-block 4-byte tail → 6ca4ecb15c5f91e1
   - Expected: _u64_to_hex(siphash24(_std_key(), _msg(60))) equals `6ca4ecb15c5f91e1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=60 multi-block 4-byte tail → 6ca4ecb15c5f91e1")
# vecs[60] = {0xe1,0x91,0x5f,0x5c,0xb1,0xec,0xa4,0x6c} LE → 0x6ca4ecb15c5f91e1
expect(_u64_to_hex(siphash24(_std_key(), _msg(60)))).to_equal("6ca4ecb15c5f91e1")
```

</details>

#### N=63 multi-block 7-byte tail → 958a324ceb064572

- N=63 multi-block 7-byte tail → 958a324ceb064572
   - Expected: _u64_to_hex(siphash24(_std_key(), _msg(63))) equals `958a324ceb064572`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=63 multi-block 7-byte tail → 958a324ceb064572")
# vecs[63] = {0x72,0x45,0x06,0xeb,0x4c,0x32,0x8a,0x95} LE → 0x958a324ceb064572
expect(_u64_to_hex(siphash24(_std_key(), _msg(63)))).to_equal("958a324ceb064572")
```

</details>

### SipHash-1-3 reference vectors (siphasher crate)

#### N=0 empty message → abac0158050fc4dc

- N=0 empty message → abac0158050fc4dc
   - Expected: _u64_to_hex(siphash13(_std_key(), _msg(0))) equals `abac0158050fc4dc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=0 empty message → abac0158050fc4dc")
# vecs[0] = {0xdc,0xc4,0x0f,0x05,0x58,0x01,0xac,0xab} LE → 0xabac0158050fc4dc
expect(_u64_to_hex(siphash13(_std_key(), _msg(0)))).to_equal("abac0158050fc4dc")
```

</details>

#### N=8 one full block → 369095118d299a8e

- N=8 one full block → 369095118d299a8e
   - Expected: _u64_to_hex(siphash13(_std_key(), _msg(8))) equals `369095118d299a8e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=8 one full block → 369095118d299a8e")
# vecs[8] = {0x8e,0x9a,0x29,0x8d,0x11,0x95,0x90,0x36} LE → 0x369095118d299a8e
expect(_u64_to_hex(siphash13(_std_key(), _msg(8)))).to_equal("369095118d299a8e")
```

</details>

#### N=15 one block + 7-byte tail → d320d86d2a519956

- N=15 one block + 7-byte tail → d320d86d2a519956
   - Expected: _u64_to_hex(siphash13(_std_key(), _msg(15))) equals `d320d86d2a519956`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=15 one block + 7-byte tail → d320d86d2a519956")
# vecs[15] = {0x56,0x99,0x51,0x2a,0x6d,0xd8,0x20,0xd3} LE → 0xd320d86d2a519956
expect(_u64_to_hex(siphash13(_std_key(), _msg(15)))).to_equal("d320d86d2a519956")
```

</details>

#### N=60 multi-block 4-byte tail → f6f4e6bcf7a644ee

- N=60 multi-block 4-byte tail → f6f4e6bcf7a644ee
   - Expected: _u64_to_hex(siphash13(_std_key(), _msg(60))) equals `f6f4e6bcf7a644ee`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=60 multi-block 4-byte tail → f6f4e6bcf7a644ee")
# vecs[60] = {0xee,0x44,0xa6,0xf7,0xbc,0xe6,0xf4,0xf6} LE → 0xf6f4e6bcf7a644ee
expect(_u64_to_hex(siphash13(_std_key(), _msg(60)))).to_equal("f6f4e6bcf7a644ee")
```

</details>

#### N=63 multi-block 7-byte tail → 9d199062b7bbb3a8

- N=63 multi-block 7-byte tail → 9d199062b7bbb3a8
   - Expected: _u64_to_hex(siphash13(_std_key(), _msg(63))) equals `9d199062b7bbb3a8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("N=63 multi-block 7-byte tail → 9d199062b7bbb3a8")
# vecs[63] = {0xa8,0xb3,0xbb,0xb7,0x62,0x90,0x19,0x9d} LE → 0x9d199062b7bbb3a8
expect(_u64_to_hex(siphash13(_std_key(), _msg(63)))).to_equal("9d199062b7bbb3a8")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/siphash_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SipHash-2-4 reference vectors (Aumasson & Bernstein 2012), SipHash-1-3 reference vectors (siphasher crate).
- SipHash-2-4 reference vectors (Aumasson & Bernstein 2012)
- SipHash-1-3 reference vectors (siphasher crate)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a76ab56700f56ab7f736eb666f191f1b3bfd4d42e5b1f07520bcfc1342b99a80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a76ab56700f56ab7f736eb666f191f1b3bfd4d42e5b1f07520bcfc1342b99a80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a76ab56700f56ab7f736eb666f191f1b3bfd4d42e5b1f07520bcfc1342b99a80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/siphash_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/siphash_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/siphash_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/siphash_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/siphash_kat_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'N=0 empty message → 726fdb47dd0e0e31' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/siphash_kat_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'N=8 one full block → 93f5f5799a932462' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/siphash_kat_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'N=15 one block + 7-byte tail → a129ca6149be45e5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
