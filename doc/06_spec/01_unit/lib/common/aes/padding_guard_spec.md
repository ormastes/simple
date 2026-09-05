# Padding Guard Specification

> Tests covering AES PKCS7 padding guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Padding Guard Specification

## Scenarios

### AES PKCS7 padding guards

#### pads valid data

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pads valid data


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads valid data")
assert_equal(pkcs7_pad([1, 2, 3], 4).unwrap(), [1, 2, 3, 1])
```

</details>

#### pads a block-aligned input with a whole extra block

- pads a block-aligned input with a whole extra block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads a block-aligned input with a whole extra block")
assert_equal(pkcs7_pad([1, 2, 3, 4], 4).unwrap(), [1, 2, 3, 4, 4, 4, 4, 4])
```

</details>

#### rejects invalid block sizes

- rejects invalid block sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid block sizes")
assert_nil(pkcs7_pad([1, 2, 3], 0))
assert_nil(pkcs7_pad([1, 2, 3], -1))
assert_nil(pkcs7_pad([1, 2, 3], 256))
```

</details>

#### unpads valid padding

- unpads valid padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unpads valid padding")
assert_equal(pkcs7_unpad([1, 2, 2, 2], 4).unwrap(), [1, 2])
```

</details>

#### unpads a full block of padding to the empty list

- unpads a full block of padding to the empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unpads a full block of padding to the empty list")
assert_equal(pkcs7_unpad([4, 4, 4, 4], 4).unwrap(), [])
```

</details>

#### round-trips pad then unpad

- round-trips pad then unpad


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips pad then unpad")
assert_equal(pkcs7_unpad(pkcs7_pad([9, 8, 7], 4).unwrap(), 4).unwrap(), [9, 8, 7])
```

</details>

#### REJECTS padding whose bytes do not all match the pad length

- REJECTS padding whose bytes do not all match the pad length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS padding whose bytes do not all match the pad length")
assert_nil(pkcs7_unpad([1, 2, 3, 2], 4))
assert_nil(pkcs7_unpad([1, 5, 3, 3], 4))
```

</details>

#### REJECTS a zero pad length

- REJECTS a zero pad length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a zero pad length")
assert_nil(pkcs7_unpad([1, 2, 3, 0], 4))
```

</details>

#### REJECTS a pad length larger than the block size

- REJECTS a pad length larger than the block size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a pad length larger than the block size")
assert_nil(pkcs7_unpad([1, 2, 3, 9], 4))
assert_nil(pkcs7_unpad([1, 2, 3, 5], 4))
```

</details>

#### REJECTS input that is not a whole number of blocks

- REJECTS input that is not a whole number of blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS input that is not a whole number of blocks")
assert_nil(pkcs7_unpad([1, 2, 1], 4))
```

</details>

#### REJECTS empty input

- REJECTS empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS empty input")
assert_nil(pkcs7_unpad([], 4))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/aes/padding_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES PKCS7 padding guards.
- AES PKCS7 padding guards

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

- Canonical SPipe generation for source `374adff38dab362f5b606e389508f8a16a5bba591e362c65707dad5231ff16c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `374adff38dab362f5b606e389508f8a16a5bba591e362c65707dad5231ff16c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `374adff38dab362f5b606e389508f8a16a5bba591e362c65707dad5231ff16c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/aes/padding_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/aes/padding_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/aes/padding_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/aes/padding_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/aes/padding_guard_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pads valid data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/aes/padding_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pads a block-aligned input with a whole extra block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/aes/padding_guard_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid block sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
