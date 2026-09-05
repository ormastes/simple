# adler32_spec

> Purpose: Prove that Adler-32 one-shot KATs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# adler32_spec

Purpose: Prove that Adler-32 one-shot KATs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/adler32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Adler-32 one-shot KATs.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Adler-32 one-shot KATs

#### empty input -> 0x00000001 (A=1, B=0)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty input -> 0x00000001 (A=1, B=0)
- Verify: empty input -> 0x00000001 (A=1, B=0)
   - Expected: adler32(_empty()) equals `0x00000001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input -> 0x00000001 (A=1, B=0)")
step("Verify: empty input -> 0x00000001 (A=1, B=0)")
# @req: REQ-OS-CRYPTO-001
expect(adler32(_empty())).to_equal(0x00000001)
```

</details>

#### \

- \
   - Expected: adler32(_abc()) equals `0x024D0127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(adler32(_abc())).to_equal(0x024D0127)
```

</details>

#### \

- \
   - Expected: adler32(_wikipedia()) equals `0x11E60398`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(adler32(_wikipedia())).to_equal(0x11E60398)
```

</details>

#### 6000-byte benchmark pattern crosses the classic 5552-byte reduction window

- 6000-byte benchmark pattern crosses the classic 5552-byte reduction window
- Verify: 6000-byte benchmark pattern crosses the classic 5552-byte reduction window
   - Expected: adler32(_pattern_6000()) equals `0x3B74AB6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("6000-byte benchmark pattern crosses the classic 5552-byte reduction window")
step("Verify: 6000-byte benchmark pattern crosses the classic 5552-byte reduction window")
expect(adler32(_pattern_6000())).to_equal(0x3B74AB6E)
```

</details>

### Adler-32 streaming API

#### update with empty data is identity

- update with empty data is identity
- Verify: update with empty data is identity
   - Expected: s1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update with empty data is identity")
step("Verify: update with empty data is identity")
val s0 = 1
val s1 = adler32_update(s0, _empty())
expect(s1).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### split \

- split \
   - Expected: s2 equals `adler32(_abc())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("split \")
val s0 = 1
val s1 = adler32_update(s0, _abc_first())
val s2 = adler32_update(s1, _abc_rest())
expect(s2).to_equal(adler32(_abc()))
```

</details>

#### full \

- full \
   - Expected: s1 equals `0x024D0127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full \")
val s0 = 1
val s1 = adler32_update(s0, _abc())
expect(s1).to_equal(0x024D0127)
```

</details>

### Fletcher-32 one-shot KATs

#### empty input -> 0

- empty input -> 0
- Verify: empty input -> 0
   - Expected: fletcher32(_empty()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty input -> 0")
step("Verify: empty input -> 0")
expect(fletcher32(_empty())).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### \

- \
   - Expected: fletcher32(_abcd()) equals `0x2926C6C4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(fletcher32(_abcd())).to_equal(0x2926C6C4)
```

</details>

#### \

- \
   - Expected: fletcher32(_abc()) equals `0xC52562C4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
expect(fletcher32(_abc())).to_equal(0xC52562C4)
```

</details>

### Fletcher-32 streaming API

#### update with empty data is identity

- update with empty data is identity
- Verify: update with empty data is identity
   - Expected: r[0] equals `0`
   - Expected: r[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update with empty data is identity")
step("Verify: update with empty data is identity")
val r = fletcher32_update(0, 0, _empty())
expect(r[0]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(r[1]).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### split \

- split \
   - Expected: (r2[1] << 16) | r2[0] equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("split \")
val r1 = fletcher32_update(0, 0, _abcd_first())
val r2 = fletcher32_update(r1[0], r1[1], _abcd_rest())
val expected = fletcher32(_abcd())
expect((r2[1] << 16) | r2[0]).to_equal(expected)
```

</details>

#### full \

- full \
   - Expected: (r[1] << 16) | r[0] equals `0x2926C6C4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full \")
val r = fletcher32_update(0, 0, _abcd())
expect((r[1] << 16) | r[0]).to_equal(0x2926C6C4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-CRYPTO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02fa78e13124976ee1252736eb3d07b9cbd00f69d5d5b96f94e69336ab96d63e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02fa78e13124976ee1252736eb3d07b9cbd00f69d5d5b96f94e69336ab96d63e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02fa78e13124976ee1252736eb3d07b9cbd00f69d5d5b96f94e69336ab96d63e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/adler32_spec.spl
mirror: doc/06_spec/unit/os/crypto/adler32_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/adler32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/adler32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/adler32_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty input -> 0x00000001 (A=1, B=0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/adler32_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/adler32_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
