# RV64 Memory Operations Unit Tests

> Unit tests for all load/store variants: LB, LH, LW, LD, LBU, LHU, LWU, SB, SH, SW, SD. Tests byte-level memory access with sign/zero extension.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Memory Operations Unit Tests

Unit tests for all load/store variants: LB, LH, LW, LD, LBU, LHU, LWU, SB, SH, SW, SD. Tests byte-level memory access with sign/zero extension.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-MEMOPS-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for all load/store variants: LB, LH, LW, LD, LBU, LHU, LWU,
SB, SH, SW, SD. Tests byte-level memory access with sign/zero extension.

## Scenarios

### SB (Store Byte)

#### stores lowest byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores lowest byte
   - Expected: ram.read8(0).value equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores lowest byte")
var ram = Rv64Ram.create(16)
ram.write8(0, 0xAB)
expect(ram.read8(0).value).to_equal(0xAB)
```

</details>

#### stores only lower 8 bits

- stores only lower 8 bits
   - Expected: ram.read8(0).value equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores only lower 8 bits")
var ram = Rv64Ram.create(16)
ram.write8(0, 0x1AB)
expect(ram.read8(0).value).to_equal(0xAB)
```

</details>

#### stores to specific address

- stores to specific address
   - Expected: ram.read8(5).value equals `0xFF`
   - Expected: ram.read8(4).value equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores to specific address")
var ram = Rv64Ram.create(16)
ram.write8(5, 0xFF)
expect(ram.read8(5).value).to_equal(0xFF)
expect(ram.read8(4).value).to_equal(0x00)
```

</details>

### SH (Store Halfword)

#### stores 16-bit little-endian

- stores 16-bit little-endian
   - Expected: ram.read8(0).value equals `0xEF`
   - Expected: ram.read8(1).value equals `0xBE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores 16-bit little-endian")
var ram = Rv64Ram.create(16)
ram.write16(0, 0xBEEF)
expect(ram.read8(0).value).to_equal(0xEF)
expect(ram.read8(1).value).to_equal(0xBE)
```

</details>

#### read16 returns correct value

- read16 returns correct value
   - Expected: ram.read16(2).value equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read16 returns correct value")
var ram = Rv64Ram.create(16)
ram.write16(2, 0x1234)
expect(ram.read16(2).value).to_equal(0x1234)
```

</details>

### SW (Store Word)

#### stores 32-bit little-endian

- stores 32-bit little-endian
   - Expected: ram.read32(0).value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores 32-bit little-endian")
var ram = Rv64Ram.create(16)
ram.write32(0, 0xDEADBEEF)
expect(ram.read32(0).value).to_equal(0xDEADBEEF)
```

</details>

#### bytes stored in correct order

- bytes stored in correct order
   - Expected: ram.read8(0).value equals `0x01`
   - Expected: ram.read8(1).value equals `0x02`
   - Expected: ram.read8(2).value equals `0x03`
   - Expected: ram.read8(3).value equals `0x04`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bytes stored in correct order")
var ram = Rv64Ram.create(16)
ram.write32(0, 0x04030201)
expect(ram.read8(0).value).to_equal(0x01)
expect(ram.read8(1).value).to_equal(0x02)
expect(ram.read8(2).value).to_equal(0x03)
expect(ram.read8(3).value).to_equal(0x04)
```

</details>

### SD (Store Doubleword)

#### stores 64-bit little-endian

- stores 64-bit little-endian
   - Expected: ram.read64(0).value equals `0xDEADBEEFCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores 64-bit little-endian")
var ram = Rv64Ram.create(16)
ram.write64(0, 0xDEADBEEFCAFEBABE)
expect(ram.read64(0).value).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### bytes stored in correct order

- bytes stored in correct order
   - Expected: ram.read8(0).value equals `0x01`
   - Expected: ram.read8(7).value equals `0x08`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bytes stored in correct order")
var ram = Rv64Ram.create(16)
ram.write64(0, 0x0807060504030201)
expect(ram.read8(0).value).to_equal(0x01)
expect(ram.read8(7).value).to_equal(0x08)
```

</details>

### LB (Load Byte — sign-extended)

#### LB positive byte

- LB positive byte
   - Expected: _sign_extend_8(raw) equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LB positive byte")
var ram = Rv64Ram.create(16)
ram.write8(0, 0x7F)
val raw = ram.read8(0).value
expect(_sign_extend_8(raw)).to_equal(0x7F)
```

</details>

#### LB negative byte sign-extends to 64 bits

- LB negative byte sign-extends to 64 bits
   - Expected: _sign_extend_8(raw) equals `0xFFFFFFFFFFFFFF80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LB negative byte sign-extends to 64 bits")
var ram = Rv64Ram.create(16)
ram.write8(0, 0x80)
val raw = ram.read8(0).value
expect(_sign_extend_8(raw)).to_equal(0xFFFFFFFFFFFFFF80)
```

</details>

#### LB 0xFF sign-extends to -1

- LB 0xFF sign-extends to -1
   - Expected: _sign_extend_8(raw) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LB 0xFF sign-extends to -1")
var ram = Rv64Ram.create(16)
ram.write8(0, 0xFF)
val raw = ram.read8(0).value
expect(_sign_extend_8(raw)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### LBU (Load Byte Unsigned — zero-extended)

#### LBU positive byte

- LBU positive byte
   - Expected: ram.read8(0).value equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LBU positive byte")
var ram = Rv64Ram.create(16)
ram.write8(0, 0x7F)
expect(ram.read8(0).value).to_equal(0x7F)
```

</details>

#### LBU high byte stays unsigned

- LBU high byte stays unsigned
   - Expected: ram.read8(0).value equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LBU high byte stays unsigned")
var ram = Rv64Ram.create(16)
ram.write8(0, 0xFF)
expect(ram.read8(0).value).to_equal(0xFF)
```

</details>

#### LBU 0x80 stays positive

- LBU 0x80 stays positive
   - Expected: ram.read8(0).value equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LBU 0x80 stays positive")
var ram = Rv64Ram.create(16)
ram.write8(0, 0x80)
expect(ram.read8(0).value).to_equal(0x80)
```

</details>

### LH (Load Halfword — sign-extended)

#### LH positive halfword

- LH positive halfword
   - Expected: _sign_extend_16(raw) equals `0x7FFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LH positive halfword")
var ram = Rv64Ram.create(16)
ram.write16(0, 0x7FFF)
val raw = ram.read16(0).value
expect(_sign_extend_16(raw)).to_equal(0x7FFF)
```

</details>

#### LH negative halfword sign-extends

- LH negative halfword sign-extends
   - Expected: _sign_extend_16(raw) equals `0xFFFFFFFFFFFF8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LH negative halfword sign-extends")
var ram = Rv64Ram.create(16)
ram.write16(0, 0x8000)
val raw = ram.read16(0).value
expect(_sign_extend_16(raw)).to_equal(0xFFFFFFFFFFFF8000)
```

</details>

#### LH 0xFFFF sign-extends to -1

- LH 0xFFFF sign-extends to -1
   - Expected: _sign_extend_16(raw) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LH 0xFFFF sign-extends to -1")
var ram = Rv64Ram.create(16)
ram.write16(0, 0xFFFF)
val raw = ram.read16(0).value
expect(_sign_extend_16(raw)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### LHU (Load Halfword Unsigned)

#### LHU stays unsigned

- LHU stays unsigned
   - Expected: ram.read16(0).value equals `0xFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LHU stays unsigned")
var ram = Rv64Ram.create(16)
ram.write16(0, 0xFFFF)
expect(ram.read16(0).value).to_equal(0xFFFF)
```

</details>

#### LHU 0x8000 stays positive

- LHU 0x8000 stays positive
   - Expected: ram.read16(0).value equals `0x8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LHU 0x8000 stays positive")
var ram = Rv64Ram.create(16)
ram.write16(0, 0x8000)
expect(ram.read16(0).value).to_equal(0x8000)
```

</details>

### LW (Load Word — sign-extended)

#### LW positive word

- LW positive word
   - Expected: _sign_extend_32(raw) equals `0x7FFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LW positive word")
var ram = Rv64Ram.create(16)
ram.write32(0, 0x7FFFFFFF)
val raw = ram.read32(0).value
expect(_sign_extend_32(raw)).to_equal(0x7FFFFFFF)
```

</details>

#### LW negative word sign-extends

- LW negative word sign-extends
   - Expected: _sign_extend_32(raw) equals `0xFFFFFFFF80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LW negative word sign-extends")
var ram = Rv64Ram.create(16)
ram.write32(0, 0x80000000)
val raw = ram.read32(0).value
expect(_sign_extend_32(raw)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### LW 0xFFFFFFFF sign-extends to -1

- LW 0xFFFFFFFF sign-extends to -1
   - Expected: _sign_extend_32(raw) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LW 0xFFFFFFFF sign-extends to -1")
var ram = Rv64Ram.create(16)
ram.write32(0, 0xFFFFFFFF)
val raw = ram.read32(0).value
expect(_sign_extend_32(raw)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### LWU (Load Word Unsigned)

#### LWU stays unsigned

- LWU stays unsigned
   - Expected: ram.read32(0).value equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LWU stays unsigned")
var ram = Rv64Ram.create(16)
ram.write32(0, 0xFFFFFFFF)
expect(ram.read32(0).value).to_equal(0xFFFFFFFF)
```

</details>

#### LWU 0x80000000 stays positive

- LWU 0x80000000 stays positive
   - Expected: ram.read32(0).value equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LWU 0x80000000 stays positive")
var ram = Rv64Ram.create(16)
ram.write32(0, 0x80000000)
expect(ram.read32(0).value).to_equal(0x80000000)
```

</details>

### LD (Load Doubleword)

#### LD full 64-bit value

- LD full 64-bit value
   - Expected: ram.read64(0).value equals `0xDEADBEEFCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LD full 64-bit value")
var ram = Rv64Ram.create(16)
ram.write64(0, 0xDEADBEEFCAFEBABE)
expect(ram.read64(0).value).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### LD zero

- LD zero
   - Expected: ram.read64(0).value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LD zero")
var ram = Rv64Ram.create(16)
expect(ram.read64(0).value).to_equal(0)
```

</details>

### Out-of-Bounds Access

#### read beyond bounds returns fault

- read beyond bounds returns fault
   - Expected: result.fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read beyond bounds returns fault")
var ram = Rv64Ram.create(8)
val result = ram.read8(8)
expect(result.fault).to_equal(true)
```

</details>

#### write beyond bounds returns fault

- write beyond bounds returns fault
   - Expected: result.fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write beyond bounds returns fault")
var ram = Rv64Ram.create(8)
val result = ram.write8(8, 0xFF)
expect(result.fault).to_equal(true)
```

</details>

#### 64-bit access at boundary faults

- 64-bit access at boundary faults
   - Expected: result.fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("64-bit access at boundary faults")
var ram = Rv64Ram.create(8)
val result = ram.read64(1)
expect(result.fault).to_equal(true)
```

</details>

### Mixed Width Operations

#### write word then read bytes

- write word then read bytes
   - Expected: ram.read8(0).value equals `0xEF`
   - Expected: ram.read8(1).value equals `0xBE`
   - Expected: ram.read8(2).value equals `0xAD`
   - Expected: ram.read8(3).value equals `0xDE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write word then read bytes")
var ram = Rv64Ram.create(16)
ram.write32(0, 0xDEADBEEF)
expect(ram.read8(0).value).to_equal(0xEF)
expect(ram.read8(1).value).to_equal(0xBE)
expect(ram.read8(2).value).to_equal(0xAD)
expect(ram.read8(3).value).to_equal(0xDE)
```

</details>

#### write bytes then read word

- write bytes then read word
   - Expected: ram.read32(0).value equals `0x04030201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write bytes then read word")
var ram = Rv64Ram.create(16)
ram.write8(0, 0x01)
ram.write8(1, 0x02)
ram.write8(2, 0x03)
ram.write8(3, 0x04)
expect(ram.read32(0).value).to_equal(0x04030201)
```

</details>

#### write double then read words

- write double then read words
   - Expected: ram.read32(0).value equals `0xDEADBEEF`
   - Expected: ram.read32(4).value equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write double then read words")
var ram = Rv64Ram.create(16)
ram.write64(0, 0xCAFEBABEDEADBEEF)
expect(ram.read32(0).value).to_equal(0xDEADBEEF)
expect(ram.read32(4).value).to_equal(0xCAFEBABE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `9e174632099344ecadef110b679117b21fb3a2a34ed982437f53536c1ddaa6d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e174632099344ecadef110b679117b21fb3a2a34ed982437f53536c1ddaa6d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e174632099344ecadef110b679117b21fb3a2a34ed982437f53536c1ddaa6d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl
mirror: doc/06_spec/unit/hardware/rv64gc/rv64_memory_ops_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv64gc/rv64_memory_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv64gc/rv64_memory_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores lowest byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores only lower 8 bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores to specific address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
