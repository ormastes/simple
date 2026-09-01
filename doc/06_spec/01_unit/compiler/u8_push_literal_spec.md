# U8 Push Literal Specification

> Tests covering u8 push literal.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U8 Push Literal Specification

## Scenarios

### u8 push literal

#### direct push matches workaround push byte-for-byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- direct push matches workaround push byte-for-byte
   - Expected: direct.len() equals `8`
   - Expected: workaround.len() equals `8`
   - Expected: direct[0] equals `workaround[0]`
   - Expected: direct[1] equals `workaround[1]`
   - Expected: direct[2] equals `workaround[2]`
   - Expected: direct[3] equals `workaround[3]`
   - Expected: direct[4] equals `workaround[4]`
   - Expected: direct[5] equals `workaround[5]`
   - Expected: direct[6] equals `workaround[6]`
   - Expected: direct[7] equals `workaround[7]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("direct push matches workaround push byte-for-byte")
val direct = build_key_direct()
val workaround = build_key_workaround()
expect(direct.len()).to_equal(8)
expect(workaround.len()).to_equal(8)
expect(direct[0]).to_equal(workaround[0])
expect(direct[1]).to_equal(workaround[1])
expect(direct[2]).to_equal(workaround[2])
expect(direct[3]).to_equal(workaround[3])
expect(direct[4]).to_equal(workaround[4])
expect(direct[5]).to_equal(workaround[5])
expect(direct[6]).to_equal(workaround[6])
expect(direct[7]).to_equal(workaround[7])
```

</details>

#### direct push preserves exact values

- direct push preserves exact values
   - Expected: direct[0] equals `0x01u8`
   - Expected: direct[1] equals `0x23u8`
   - Expected: direct[2] equals `0x45u8`
   - Expected: direct[3] equals `0x67u8`
   - Expected: direct[4] equals `0x89u8`
   - Expected: direct[5] equals `0xABu8`
   - Expected: direct[6] equals `0xCDu8`
   - Expected: direct[7] equals `0xEFu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("direct push preserves exact values")
val direct = build_key_direct()
expect(direct[0]).to_equal(0x01u8)
expect(direct[1]).to_equal(0x23u8)
expect(direct[2]).to_equal(0x45u8)
expect(direct[3]).to_equal(0x67u8)
expect(direct[4]).to_equal(0x89u8)
expect(direct[5]).to_equal(0xABu8)
expect(direct[6]).to_equal(0xCDu8)
expect(direct[7]).to_equal(0xEFu8)
```

</details>

#### in-block direct push preserves value

- in-block direct push preserves value
   - Expected: arr[0] equals `0x42u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("in-block direct push preserves value")
var arr: [u8] = []
arr.push(0x42u8)
expect(arr[0]).to_equal(0x42u8)
```

</details>

#### push decimal u8 literal

- push decimal u8 literal
   - Expected: arr[0] equals `65u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("push decimal u8 literal")
var arr: [u8] = []
arr.push(65u8)
expect(arr[0]).to_equal(65u8)
```

</details>

#### push zero literal

- push zero literal
   - Expected: arr[0] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("push zero literal")
var arr: [u8] = []
arr.push(0u8)
expect(arr[0]).to_equal(0u8)
```

</details>

#### push max u8 literal

- push max u8 literal
   - Expected: arr[0] equals `255u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("push max u8 literal")
var arr: [u8] = []
arr.push(255u8)
expect(arr[0]).to_equal(255u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u8_push_literal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering u8 push literal.
- u8 push literal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d2b6c283bb95ea9d1d1de9a84ffbe7d1e3a7eb7724bcd9538757a4c35ffd167`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d2b6c283bb95ea9d1d1de9a84ffbe7d1e3a7eb7724bcd9538757a4c35ffd167`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d2b6c283bb95ea9d1d1de9a84ffbe7d1e3a7eb7724bcd9538757a4c35ffd167`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/u8_push_literal_spec.spl
mirror: doc/06_spec/01_unit/compiler/u8_push_literal_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/u8_push_literal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/u8_push_literal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/u8_push_literal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/u8_push_literal_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'direct push matches workaround push byte-for-byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u8_push_literal_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'direct push preserves exact values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u8_push_literal_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'in-block direct push preserves value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
