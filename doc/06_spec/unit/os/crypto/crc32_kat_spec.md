# Crc32 Kat Specification

> Tests covering CRC-32 IEEE 802.3 one-shot KATs, CRC-32C Castagnoli one-shot KATs, CRC-32 IEEE 802.3 streaming API, CRC-32C Castagnoli streaming API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crc32 Kat Specification

## Scenarios

### CRC-32 IEEE 802.3 one-shot KATs

#### empty input → 0x00000000

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty input → 0x00000000
   - Expected: crc32(_empty()) equals `0x00000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input → 0x00000000")
expect(crc32(_empty())).to_equal(0x00000000)
```

</details>

#### \

- \
   - Expected: crc32(_abc()) equals `0x352441C2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(crc32(_abc())).to_equal(0x352441C2)
```

</details>

#### \

- \
   - Expected: crc32(_check_sequence()) equals `0xCBF43926`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(crc32(_check_sequence())).to_equal(0xCBF43926)
```

</details>

### CRC-32C Castagnoli one-shot KATs

#### empty input → 0x00000000

- empty input → 0x00000000
   - Expected: crc32c(_empty()) equals `0x00000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input → 0x00000000")
expect(crc32c(_empty())).to_equal(0x00000000)
```

</details>

#### \

- \
   - Expected: crc32c(_abc()) equals `0x364B3FB7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(crc32c(_abc())).to_equal(0x364B3FB7)
```

</details>

#### \

- \
   - Expected: crc32c(_check_sequence()) equals `0xE3069283`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(crc32c(_check_sequence())).to_equal(0xE3069283)
```

</details>

### CRC-32 IEEE 802.3 streaming API

#### streaming \

- streaming \
   - Expected: result equals `0x352441C2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streaming \")
val s1 = crc32_update(crc32_init(), _abc_part1())
val s2 = crc32_update(s1, _abc_part2())
val result = crc32_finalize(s2)
expect(result).to_equal(0x352441C2)
```

</details>

#### streaming empty matches one-shot

- streaming empty matches one-shot
   - Expected: result equals `0x00000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streaming empty matches one-shot")
val result = crc32_finalize(crc32_update(crc32_init(), _empty()))
expect(result).to_equal(0x00000000)
```

</details>

### CRC-32C Castagnoli streaming API

#### streaming \

- streaming \
   - Expected: result equals `0x364B3FB7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streaming \")
val s1 = crc32c_update(crc32c_init(), _abc_part1())
val s2 = crc32c_update(s1, _abc_part2())
val result = crc32c_finalize(s2)
expect(result).to_equal(0x364B3FB7)
```

</details>

#### streaming empty matches one-shot

- streaming empty matches one-shot
   - Expected: result equals `0x00000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("streaming empty matches one-shot")
val result = crc32c_finalize(crc32c_update(crc32c_init(), _empty()))
expect(result).to_equal(0x00000000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/crc32_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CRC-32 IEEE 802.3 one-shot KATs, CRC-32C Castagnoli one-shot KATs, CRC-32 IEEE 802.3 streaming API, CRC-32C Castagnoli streaming API.
- CRC-32 IEEE 802.3 one-shot KATs
- CRC-32C Castagnoli one-shot KATs
- CRC-32 IEEE 802.3 streaming API
- CRC-32C Castagnoli streaming API

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

- Canonical SPipe generation for source `4f502c30a2cdef971de84481a431868538c8f247ee6dc3db0197172d0570ef25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f502c30a2cdef971de84481a431868538c8f247ee6dc3db0197172d0570ef25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f502c30a2cdef971de84481a431868538c8f247ee6dc3db0197172d0570ef25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/crc32_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/crc32_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/crc32_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/crc32_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/crc32_kat_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty input → 0x00000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/crc32_kat_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/crc32_kat_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
