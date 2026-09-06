# Sha384 Kat Specification

> Tests covering SHA-384 — FIPS 180-4 known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha384 Kat Specification

## Scenarios

### SHA-384 — FIPS 180-4 known-answer vectors

#### padding empty: byte[0]=0x80, length=128

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- padding empty: byte[0]=0x80, length=128
   - Expected: padded.len() equals `128`
   - Expected: padded[0] equals `0x80`
   - Expected: padded[1] equals `0x00`
   - Expected: padded[127] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("padding empty: byte[0]=0x80, length=128")
val padded = _sha384_pad(_empty_bytes())
expect(padded.len()).to_equal(128)
expect(padded[0]).to_equal(0x80)
expect(padded[1]).to_equal(0x00)
expect(padded[127]).to_equal(0x00)
```

</details>

#### diag: w[0] for empty input = 0x8000000000000000

- diag: w[0] for empty input = 0x8000000000000000
   - Expected: _sha384_diag_w0(_empty_bytes()) equals `0x8000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diag: w[0] for empty input = 0x8000000000000000")
expect(_sha384_diag_w0(_empty_bytes())).to_equal(0x8000000000000000)
```

</details>

#### diag: h[0] = 0xcbbb9d5dc1059ed8

- diag: h[0] = 0xcbbb9d5dc1059ed8
   - Expected: _sha384_diag_h0() equals `0xCBBB9D5DC1059ED8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diag: h[0] = 0xcbbb9d5dc1059ed8")
expect(_sha384_diag_h0()).to_equal(0xCBBB9D5DC1059ED8)
```

</details>

#### diag: big_sigma0(SHA-384 h[0]) == canonical 0xdb9a810738c045b1

- diag: big_sigma0(SHA-384 h[0]) == canonical 0xdb9a810738c045b1
   - Expected: _sha384_diag_big_sigma0_h0() equals `0xdb9a810738c045b1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diag: big_sigma0(SHA-384 h[0]) == canonical 0xdb9a810738c045b1")
# Regression guard for the u64-fn-param right-shift sign-extension bug
# fixed via _logical_shr64 in sha384.spl. Before fix, this returned
# 0xfffffffcb6c045b1 because (x >> 28/34/39) on a u64 fn param
# arg with bit 63 set sign-extended into the high bits. See
# doc/08_tracking/bug/u64_right_shift_fn_param_arithmetic_2026-05-02.md.
expect(_sha384_diag_big_sigma0_h0()).to_equal(0xdb9a810738c045b1)
```

</details>

#### SHA-384(\

- SHA-384(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-384(\")
expect(_bytes_hex(sha384(_empty_bytes()))).to_equal(
    "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
)
```

</details>

#### SHA-384(\

- SHA-384(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-384(\")
expect(_bytes_hex(sha384(_abc_bytes()))).to_equal(
    "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
)
```

</details>

#### SHA-384 output length is 48 bytes

- SHA-384 output length is 48 bytes
   - Expected: sha384(_abc_bytes()).len() equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-384 output length is 48 bytes")
expect(sha384(_abc_bytes()).len()).to_equal(48)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/sha384_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-384 — FIPS 180-4 known-answer vectors.
- SHA-384 — FIPS 180-4 known-answer vectors

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

- Canonical SPipe generation for source `6728fb41c0852fdbf16f1fc73f422d02dbfca155c8412f1f0a038f0b4b06f83d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6728fb41c0852fdbf16f1fc73f422d02dbfca155c8412f1f0a038f0b4b06f83d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6728fb41c0852fdbf16f1fc73f422d02dbfca155c8412f1f0a038f0b4b06f83d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/sha384_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/sha384_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/sha384_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/sha384_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/sha384_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/sha384_kat_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'padding empty: byte[0]=0x80, length=128' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sha384_kat_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diag: w[0] for empty input = 0x8000000000000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sha384_kat_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diag: h[0] = 0xcbbb9d5dc1059ed8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
