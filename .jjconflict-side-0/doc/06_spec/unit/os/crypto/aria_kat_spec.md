# Aria Kat Specification

> Tests covering ARIA RFC 5794 §B.1 — ARIA-128, ARIA RFC 5794 §B.3 — ARIA-256.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aria Kat Specification

## Scenarios

### ARIA RFC 5794 §B.1 — ARIA-128

#### encrypt → c6ecd08e22c30abdb215cf74e2075e6e

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encrypt → c6ecd08e22c30abdb215cf74e2075e6e
   - Expected: _bytes_hex(ct) equals `c6ecd08e22c30abdb215cf74e2075e6e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt → c6ecd08e22c30abdb215cf74e2075e6e")
val ct = aria_encrypt_block(_b1_key(), _b1_pt())
expect(_bytes_hex(ct)).to_equal("c6ecd08e22c30abdb215cf74e2075e6e")
```

</details>

#### output is 16 bytes

- output is 16 bytes
   - Expected: ct.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output is 16 bytes")
val ct = aria_encrypt_block(_b1_key(), _b1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trips to plaintext

- decrypt round-trips to plaintext
   - Expected: _bytes_hex(pt) equals `_bytes_hex(_b1_pt())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt round-trips to plaintext")
val ct = aria_encrypt_block(_b1_key(), _b1_pt())
val pt = aria_decrypt_block(_b1_key(), ct)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_b1_pt()))
```

</details>

#### decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb

- decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb
   - Expected: _bytes_hex(pt) equals `11111111aaaaaaaa11111111bbbbbbbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb")
val pt = aria_decrypt_block(_b1_key(), _b1_ct())
expect(_bytes_hex(pt)).to_equal("11111111aaaaaaaa11111111bbbbbbbb")
```

</details>

### ARIA RFC 5794 §B.3 — ARIA-256

#### encrypt → 58a875e6044ad7fffa4f58420f7f442d

- encrypt → 58a875e6044ad7fffa4f58420f7f442d
   - Expected: _bytes_hex(ct) equals `58a875e6044ad7fffa4f58420f7f442d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt → 58a875e6044ad7fffa4f58420f7f442d")
val ct = aria_encrypt_block(_b3_key(), _b1_pt())
expect(_bytes_hex(ct)).to_equal("58a875e6044ad7fffa4f58420f7f442d")
```

</details>

#### output is 16 bytes

- output is 16 bytes
   - Expected: ct.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output is 16 bytes")
val ct = aria_encrypt_block(_b3_key(), _b1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trips to plaintext

- decrypt round-trips to plaintext
   - Expected: _bytes_hex(pt) equals `_bytes_hex(_b1_pt())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt round-trips to plaintext")
val ct = aria_encrypt_block(_b3_key(), _b1_pt())
val pt = aria_decrypt_block(_b3_key(), ct)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_b1_pt()))
```

</details>

#### decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb

- decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb
   - Expected: _bytes_hex(pt) equals `11111111aaaaaaaa11111111bbbbbbbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb")
val pt = aria_decrypt_block(_b3_key(), _b3_ct())
expect(_bytes_hex(pt)).to_equal("11111111aaaaaaaa11111111bbbbbbbb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/aria_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARIA RFC 5794 §B.1 — ARIA-128, ARIA RFC 5794 §B.3 — ARIA-256.
- ARIA RFC 5794 §B.1 — ARIA-128
- ARIA RFC 5794 §B.3 — ARIA-256

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `2d0e31b4ab1d9aa3a54cce7576a39cdb4bf1847ed7f203bd4e1fb25d9af06a9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d0e31b4ab1d9aa3a54cce7576a39cdb4bf1847ed7f203bd4e1fb25d9af06a9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d0e31b4ab1d9aa3a54cce7576a39cdb4bf1847ed7f203bd4e1fb25d9af06a9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/aria_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/aria_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/aria_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/aria_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/aria_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/aria_kat_spec.spl:202:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypt → c6ecd08e22c30abdb215cf74e2075e6e' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/aria_kat_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'output is 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/aria_kat_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decrypt round-trips to plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
