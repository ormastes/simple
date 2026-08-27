# Salsa20 Simd Specification

> Tests covering salsa20_8_core scalar — RFC 7914 §B.1, salsa20_8_core_x4 SIMD — RFC 7914 §B.1 (lane 0), salsa20_8_core_x4 SIMD — parity with scalar on all 4 lanes, salsa20_8_core_x4 SIMD — lane independence, salsa20_8_core_x4 SIMD — zero-block consistency, scrypt RFC 7914 §11 V1 — regression after SIMD addition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Salsa20 Simd Specification

## Scenarios

### salsa20_8_core scalar — RFC 7914 §B.1

#### scalar: RFC 7914 §B.1 vector matches byte-exact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scalar: RFC 7914 §B.1 vector matches byte-exact
   - Expected: _list_hex(out) equals `_rfc_expected_hex()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar: RFC 7914 §B.1 vector matches byte-exact")
val out = salsa20_8_core(_rfc_input())
expect(_list_hex(out)).to_equal(_rfc_expected_hex())
```

</details>

#### scalar: output length is 64 bytes

- scalar: output length is 64 bytes
   - Expected: out.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar: output length is 64 bytes")
val out = salsa20_8_core(_rfc_input())
expect(out.len()).to_equal(64)
```

</details>

### salsa20_8_core_x4 SIMD — RFC 7914 §B.1 (lane 0)

#### x4 lane 0: RFC 7914 §B.1 vector matches byte-exact

- x4 lane 0: RFC 7914 §B.1 vector matches byte-exact
   - Expected: lane0_hex equals `_rfc_expected_hex()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 lane 0: RFC 7914 §B.1 vector matches byte-exact")
# Feed the RFC input in lane 0; the other 3 lanes receive distinct data.
val out256 = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
val lane0_hex = _list_hex_range(out256, 0, 64)
expect(lane0_hex).to_equal(_rfc_expected_hex())
```

</details>

#### x4 output is 256 bytes total

- x4 output is 256 bytes total
   - Expected: out256.len() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 output is 256 bytes total")
val out256 = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(out256.len()).to_equal(256)
```

</details>

### salsa20_8_core_x4 SIMD — parity with scalar on all 4 lanes

#### x4 lane 0 == scalar(_rfc_input)

- x4 lane 0 == scalar(_rfc_input)
   - Expected: _list_hex_range(out256, 0, 64) equals `_list_hex(scalar0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 lane 0 == scalar(_rfc_input)")
val scalar0 = salsa20_8_core(_rfc_input())
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 0, 64)).to_equal(_list_hex(scalar0))
```

</details>

#### x4 lane 1 == scalar(_alt_input)

- x4 lane 1 == scalar(_alt_input)
   - Expected: _list_hex_range(out256, 64, 128) equals `_list_hex(scalar1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 lane 1 == scalar(_alt_input)")
val scalar1 = salsa20_8_core(_alt_input())
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 64, 128)).to_equal(_list_hex(scalar1))
```

</details>

#### x4 lane 2 == scalar(_incr_input)

- x4 lane 2 == scalar(_incr_input)
   - Expected: _list_hex_range(out256, 128, 192) equals `_list_hex(scalar2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 lane 2 == scalar(_incr_input)")
val scalar2 = salsa20_8_core(_incr_input())
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 128, 192)).to_equal(_list_hex(scalar2))
```

</details>

#### x4 lane 3 == scalar(_fill_input(0x42))

- x4 lane 3 == scalar(_fill_input(0x42))
   - Expected: _list_hex_range(out256, 192, 256) equals `_list_hex(scalar3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 lane 3 == scalar(_fill_input(0x42))")
val scalar3 = salsa20_8_core(_fill_input(0x42))
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 192, 256)).to_equal(_list_hex(scalar3))
```

</details>

### salsa20_8_core_x4 SIMD — lane independence

#### all 4 lane outputs are distinct

- all 4 lane outputs are distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 lane outputs are distinct")
val out256 = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
val h0 = _list_hex_range(out256, 0,   64)
val h1 = _list_hex_range(out256, 64,  128)
val h2 = _list_hex_range(out256, 128, 192)
val h3 = _list_hex_range(out256, 192, 256)
# h0 != h1 != h2 != h3 (pairwise inequalities)
expect(h0).to_not_equal(h1)
expect(h0).to_not_equal(h2)
expect(h0).to_not_equal(h3)
expect(h1).to_not_equal(h2)
expect(h1).to_not_equal(h3)
expect(h2).to_not_equal(h3)
```

</details>

### salsa20_8_core_x4 SIMD — zero-block consistency

#### x4 with 4 identical zero inputs: all 4 lanes equal the scalar zero output

- x4 with 4 identical zero inputs: all 4 lanes equal the scalar zero output
   - Expected: _list_hex_range(out256, 0,   64) equals `expected`
   - Expected: _list_hex_range(out256, 64,  128) equals `expected`
   - Expected: _list_hex_range(out256, 128, 192) equals `expected`
   - Expected: _list_hex_range(out256, 192, 256) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x4 with 4 identical zero inputs: all 4 lanes equal the scalar zero output")
val scalar_zero = salsa20_8_core(_zero_input())
val out256 = salsa20_8_core_x4(_zero_input(), _zero_input(), _zero_input(), _zero_input())
val expected = _list_hex(scalar_zero)
expect(_list_hex_range(out256, 0,   64)).to_equal(expected)
expect(_list_hex_range(out256, 64,  128)).to_equal(expected)
expect(_list_hex_range(out256, 128, 192)).to_equal(expected)
expect(_list_hex_range(out256, 192, 256)).to_equal(expected)
```

</details>

### scrypt RFC 7914 §11 V1 — regression after SIMD addition

#### V1: P=\

- V1: P=\


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1: P=\")
val out = scrypt(_empty_u8(), _empty_u8(), 16, 1, 1, 64)
expect(_bytes_hex(out)).to_equal(
    "77d6576238657b203b19ca42c18a0497f16b4844e3074ae8dfdffa3fede21442fcd0069ded0948f8326a753a0fc81f17e8d3e0fb2e0d3628cf35e20c38d18906"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/salsa20_simd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering salsa20_8_core scalar — RFC 7914 §B.1, salsa20_8_core_x4 SIMD — RFC 7914 §B.1 (lane 0), salsa20_8_core_x4 SIMD — parity with scalar on all 4 lanes, salsa20_8_core_x4 SIMD — lane independence, salsa20_8_core_x4 SIMD — zero-block consistency, scrypt RFC 7914 §11 V1 — regression after SIMD addition.
- salsa20_8_core scalar — RFC 7914 §B.1
- salsa20_8_core_x4 SIMD — RFC 7914 §B.1 (lane 0)
- salsa20_8_core_x4 SIMD — parity with scalar on all 4 lanes
- salsa20_8_core_x4 SIMD — lane independence
- salsa20_8_core_x4 SIMD — zero-block consistency
- scrypt RFC 7914 §11 V1 — regression after SIMD addition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `7b4ad395185cadd255b22e5a7271a431fee8146a8b4319642d3f525b78a21ef0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b4ad395185cadd255b22e5a7271a431fee8146a8b4319642d3f525b78a21ef0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b4ad395185cadd255b22e5a7271a431fee8146a8b4319642d3f525b78a21ef0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/salsa20_simd_spec.spl
mirror: doc/06_spec/unit/os/crypto/salsa20_simd_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/salsa20_simd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/salsa20_simd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/salsa20_simd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/salsa20_simd_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scalar: RFC 7914 §B.1 vector matches byte-exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/salsa20_simd_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scalar: output length is 64 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/salsa20_simd_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x4 lane 0: RFC 7914 §B.1 vector matches byte-exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
