# Reed Solomon Specification

> Tests covering Reed-Solomon GF(2^8) encoder KAT (n=10, k=4), Reed-Solomon GF(2^8) decoder — clean codeword, Reed-Solomon GF(2^8) decoder — 1-error correction, Reed-Solomon GF(2^8) decoder — 2-error correction, Reed-Solomon GF(2^8) decoder — 3-error correction (t=3), Reed-Solomon GF(2^8) decoder — over-capacity (4 errors > t=3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reed Solomon Specification

## Scenarios

### Reed-Solomon GF(2^8) encoder KAT (n=10, k=4)

#### produces correct parity byte 0 (0xfa)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces correct parity byte 0 (0xfa)
   - Expected: p[0].to_u64() equals `0xfau64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct parity byte 0 (0xfa)")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[0].to_u64()).to_equal(0xfau64)
```

</details>

#### produces correct parity byte 1 (0x22)

- produces correct parity byte 1 (0x22)
   - Expected: p[1].to_u64() equals `0x22u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct parity byte 1 (0x22)")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[1].to_u64()).to_equal(0x22u64)
```

</details>

#### produces correct parity byte 2 (0x1d)

- produces correct parity byte 2 (0x1d)
   - Expected: p[2].to_u64() equals `0x1du64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct parity byte 2 (0x1d)")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[2].to_u64()).to_equal(0x1du64)
```

</details>

#### produces correct parity byte 3 (0xc7)

- produces correct parity byte 3 (0xc7)
   - Expected: p[3].to_u64() equals `0xc7u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct parity byte 3 (0xc7)")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[3].to_u64()).to_equal(0xc7u64)
```

</details>

#### produces correct parity byte 4 (0x40)

- produces correct parity byte 4 (0x40)
   - Expected: p[4].to_u64() equals `0x40u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct parity byte 4 (0x40)")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[4].to_u64()).to_equal(0x40u64)
```

</details>

#### produces correct parity byte 5 (0x6f)

- produces correct parity byte 5 (0x6f)
   - Expected: p[5].to_u64() equals `0x6fu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct parity byte 5 (0x6f)")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p[5].to_u64()).to_equal(0x6fu64)
```

</details>

#### returns exactly (n-k)=6 parity bytes

- returns exactly (n-k)=6 parity bytes
   - Expected: p.len() equals `6u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exactly (n-k)=6 parity bytes")
val p = rs_gf256_encode(_data(), 10, 4)
expect(p.len()).to_equal(6u64)
```

</details>

### Reed-Solomon GF(2^8) decoder — clean codeword

#### clean codeword returns Ok

- clean codeword returns Ok
   - Expected: _decode_ok(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean codeword returns Ok")
val result = rs_gf256_decode(_codeword(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### clean codeword recovers data byte 0 (0x48)

- clean codeword recovers data byte 0 (0x48)
   - Expected: d[0].to_u64() equals `0x48u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean codeword recovers data byte 0 (0x48)")
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### clean codeword recovers data byte 1 (0x65)

- clean codeword recovers data byte 1 (0x65)
   - Expected: d[1].to_u64() equals `0x65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean codeword recovers data byte 1 (0x65)")
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[1].to_u64()).to_equal(0x65u64)
```

</details>

#### clean codeword recovers data byte 2 (0x6c)

- clean codeword recovers data byte 2 (0x6c)
   - Expected: d[2].to_u64() equals `0x6cu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean codeword recovers data byte 2 (0x6c)")
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[2].to_u64()).to_equal(0x6cu64)
```

</details>

#### clean codeword recovers data byte 3 (0x6c)

- clean codeword recovers data byte 3 (0x6c)
   - Expected: d[3].to_u64() equals `0x6cu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clean codeword recovers data byte 3 (0x6c)")
val d = _decode_data(rs_gf256_decode(_codeword(), 10, 4))
expect(d[3].to_u64()).to_equal(0x6cu64)
```

</details>

### Reed-Solomon GF(2^8) decoder — 1-error correction

#### 1-error: returns Ok

- 1-error: returns Ok
   - Expected: _decode_ok(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1-error: returns Ok")
val result = rs_gf256_decode(_corrupt1(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### 1-error: recovers data byte 0

- 1-error: recovers data byte 0
   - Expected: d[0].to_u64() equals `0x48u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1-error: recovers data byte 0")
val d = _decode_data(rs_gf256_decode(_corrupt1(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### 1-error: recovers data byte 3 (the corrupted one)

- 1-error: recovers data byte 3 (the corrupted one)
   - Expected: d[3].to_u64() equals `0x6cu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1-error: recovers data byte 3 (the corrupted one)")
val d = _decode_data(rs_gf256_decode(_corrupt1(), 10, 4))
expect(d[3].to_u64()).to_equal(0x6cu64)
```

</details>

### Reed-Solomon GF(2^8) decoder — 2-error correction

#### 2-error: returns Ok

- 2-error: returns Ok
   - Expected: _decode_ok(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2-error: returns Ok")
val result = rs_gf256_decode(_corrupt2(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### 2-error: recovers data byte 0

- 2-error: recovers data byte 0
   - Expected: d[0].to_u64() equals `0x48u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2-error: recovers data byte 0")
val d = _decode_data(rs_gf256_decode(_corrupt2(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### 2-error: recovers data byte 1 (corrupted)

- 2-error: recovers data byte 1 (corrupted)
   - Expected: d[1].to_u64() equals `0x65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2-error: recovers data byte 1 (corrupted)")
val d = _decode_data(rs_gf256_decode(_corrupt2(), 10, 4))
expect(d[1].to_u64()).to_equal(0x65u64)
```

</details>

### Reed-Solomon GF(2^8) decoder — 3-error correction (t=3)

#### 3-error: returns Ok

- 3-error: returns Ok
   - Expected: _decode_ok(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-error: returns Ok")
val result = rs_gf256_decode(_corrupt3(), 10, 4)
expect(_decode_ok(result)).to_equal(true)
```

</details>

#### 3-error: recovers data byte 0 (corrupted)

- 3-error: recovers data byte 0 (corrupted)
   - Expected: d[0].to_u64() equals `0x48u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-error: recovers data byte 0 (corrupted)")
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[0].to_u64()).to_equal(0x48u64)
```

</details>

#### 3-error: recovers data byte 1

- 3-error: recovers data byte 1
   - Expected: d[1].to_u64() equals `0x65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-error: recovers data byte 1")
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[1].to_u64()).to_equal(0x65u64)
```

</details>

#### 3-error: recovers data byte 2

- 3-error: recovers data byte 2
   - Expected: d[2].to_u64() equals `0x6cu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-error: recovers data byte 2")
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[2].to_u64()).to_equal(0x6cu64)
```

</details>

#### 3-error: recovers data byte 3

- 3-error: recovers data byte 3
   - Expected: d[3].to_u64() equals `0x6cu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("3-error: recovers data byte 3")
val d = _decode_data(rs_gf256_decode(_corrupt3(), 10, 4))
expect(d[3].to_u64()).to_equal(0x6cu64)
```

</details>

### Reed-Solomon GF(2^8) decoder — over-capacity (4 errors > t=3)

#### 4-error: returns Err (not Ok)

- 4-error: returns Err (not Ok)
   - Expected: _decode_err(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("4-error: returns Err (not Ok)")
val result = rs_gf256_decode(_corrupt4(), 10, 4)
expect(_decode_err(result)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/codec/reed_solomon_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Reed-Solomon GF(2^8) encoder KAT (n=10, k=4), Reed-Solomon GF(2^8) decoder — clean codeword, Reed-Solomon GF(2^8) decoder — 1-error correction, Reed-Solomon GF(2^8) decoder — 2-error correction, Reed-Solomon GF(2^8) decoder — 3-error correction (t=3), Reed-Solomon GF(2^8) decoder — over-capacity (4 errors > t=3).
- Reed-Solomon GF(2^8) encoder KAT (n=10, k=4)
- Reed-Solomon GF(2^8) decoder — clean codeword
- Reed-Solomon GF(2^8) decoder — 1-error correction
- Reed-Solomon GF(2^8) decoder — 2-error correction
- Reed-Solomon GF(2^8) decoder — 3-error correction (t=3)
- Reed-Solomon GF(2^8) decoder — over-capacity (4 errors > t=3)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `bdd350816db138749fe4957bd952f06ceaff638787c4df31baea26a0df2e7929`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdd350816db138749fe4957bd952f06ceaff638787c4df31baea26a0df2e7929`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdd350816db138749fe4957bd952f06ceaff638787c4df31baea26a0df2e7929`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/codec/reed_solomon_spec.spl
mirror: doc/06_spec/unit/os/codec/reed_solomon_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/codec/reed_solomon_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/codec/reed_solomon_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/codec/reed_solomon_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct parity byte 0 (0xfa)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/codec/reed_solomon_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct parity byte 1 (0x22)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/codec/reed_solomon_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces correct parity byte 2 (0x1d)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
