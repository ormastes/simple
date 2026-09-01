# Tea Specification

> Tests covering TEA — known-answer vectors, XTEA — known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tea Specification

## Scenarios

### TEA — known-answer vectors

#### TEA: encrypt zero key + zero block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TEA: encrypt zero key + zero block
   - Expected: _bytes_to_hex(ct) equals `41ea3a0a94baa940`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEA: encrypt zero key + zero block")
val ct = tea_encrypt(_zero_key(), _zero_block())
expect(_bytes_to_hex(ct)).to_equal("41ea3a0a94baa940")
```

</details>

#### TEA: ciphertext is 8 bytes

- TEA: ciphertext is 8 bytes
   - Expected: ct.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEA: ciphertext is 8 bytes")
val ct = tea_encrypt(_zero_key(), _zero_block())
expect(ct.len()).to_equal(8)
```

</details>

#### TEA: decrypt zero key + known CT recovers zero block

- TEA: decrypt zero key + known CT recovers zero block
   - Expected: _bytes_to_hex(pt) equals `0000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEA: decrypt zero key + known CT recovers zero block")
val pt = tea_decrypt(_zero_key(), _tea_zero_ct())
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### TEA: encrypt/decrypt round-trip (zero key)

- TEA: encrypt/decrypt round-trip (zero key)
   - Expected: _bytes_to_hex(pt) equals `0000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEA: encrypt/decrypt round-trip (zero key)")
val ct = tea_encrypt(_zero_key(), _zero_block())
val pt = tea_decrypt(_zero_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### TEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708

- TEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708
   - Expected: _bytes_to_hex(ct) equals `b1a1ab198c45fa5b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708")
val ct = tea_encrypt(_seq_key(), _seq_block())
expect(_bytes_to_hex(ct)).to_equal("b1a1ab198c45fa5b")
```

</details>

#### TEA: encrypt/decrypt round-trip (seq key)

- TEA: encrypt/decrypt round-trip (seq key)
   - Expected: _bytes_to_hex(pt) equals `0102030405060708`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEA: encrypt/decrypt round-trip (seq key)")
val ct = tea_encrypt(_seq_key(), _seq_block())
val pt = tea_decrypt(_seq_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0102030405060708")
```

</details>

### XTEA — known-answer vectors

#### XTEA: encrypt zero key + zero block

- XTEA: encrypt zero key + zero block
   - Expected: _bytes_to_hex(ct) equals `dee9d4d8f7131ed9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XTEA: encrypt zero key + zero block")
val ct = xtea_encrypt(_zero_key(), _zero_block())
expect(_bytes_to_hex(ct)).to_equal("dee9d4d8f7131ed9")
```

</details>

#### XTEA: ciphertext is 8 bytes

- XTEA: ciphertext is 8 bytes
   - Expected: ct.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XTEA: ciphertext is 8 bytes")
val ct = xtea_encrypt(_zero_key(), _zero_block())
expect(ct.len()).to_equal(8)
```

</details>

#### XTEA: decrypt zero key + known CT recovers zero block

- XTEA: decrypt zero key + known CT recovers zero block
   - Expected: _bytes_to_hex(pt) equals `0000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XTEA: decrypt zero key + known CT recovers zero block")
val pt = xtea_decrypt(_zero_key(), _xtea_zero_ct())
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### XTEA: encrypt/decrypt round-trip (zero key)

- XTEA: encrypt/decrypt round-trip (zero key)
   - Expected: _bytes_to_hex(pt) equals `0000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XTEA: encrypt/decrypt round-trip (zero key)")
val ct = xtea_encrypt(_zero_key(), _zero_block())
val pt = xtea_decrypt(_zero_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### XTEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708

- XTEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708
   - Expected: _bytes_to_hex(ct) equals `88870e082874d853`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XTEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708")
val ct = xtea_encrypt(_seq_key(), _seq_block())
expect(_bytes_to_hex(ct)).to_equal("88870e082874d853")
```

</details>

#### XTEA: encrypt/decrypt round-trip (seq key)

- XTEA: encrypt/decrypt round-trip (seq key)
   - Expected: _bytes_to_hex(pt) equals `0102030405060708`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XTEA: encrypt/decrypt round-trip (seq key)")
val ct = xtea_encrypt(_seq_key(), _seq_block())
val pt = xtea_decrypt(_seq_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0102030405060708")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/tea_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TEA — known-answer vectors, XTEA — known-answer vectors.
- TEA — known-answer vectors
- XTEA — known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `1c5b4815b01f986fdb0675c29c0620941248e57ab1dbfe0e4f1b162259ec9c1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c5b4815b01f986fdb0675c29c0620941248e57ab1dbfe0e4f1b162259ec9c1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c5b4815b01f986fdb0675c29c0620941248e57ab1dbfe0e4f1b162259ec9c1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/tea_spec.spl
mirror: doc/06_spec/unit/os/crypto/tea_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/tea_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/tea_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/tea_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/tea_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TEA: encrypt zero key + zero block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/tea_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TEA: ciphertext is 8 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/tea_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TEA: decrypt zero key + known CT recovers zero block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
