# Codec Decode Byte Guard Specification

> Tests covering encoding codec byte decode guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codec Decode Byte Guard Specification

## Scenarios

### encoding codec byte decode guards

#### keeps valid ASCII decode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid ASCII decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid ASCII decode")
assert_equal(decode([65, 66], Encoding.Ascii), "AB")
```

</details>

#### rejects malformed ASCII bytes as question marks

- rejects malformed ASCII bytes as question marks


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed ASCII bytes as question marks")
assert_equal(decode([-1, 300], Encoding.Ascii), "??")
```

</details>

#### keeps valid Latin-1 decode

- keeps valid Latin-1 decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid Latin-1 decode")
assert_equal(decode([65], Encoding.Latin1), "A")
```

</details>

#### rejects malformed Latin-1 bytes as question marks

- rejects malformed Latin-1 bytes as question marks


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed Latin-1 bytes as question marks")
assert_equal(decode([-1, 300], Encoding.Latin1), "??")
```

</details>

#### uses guarded decode during transcode

- uses guarded decode during transcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses guarded decode during transcode")
assert_equal(decode(transcode([-1, 300], Encoding.Latin1, Encoding.Ascii), Encoding.Ascii), "??")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering encoding codec byte decode guards.
- encoding codec byte decode guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `9882ac3ffb623285acf1370a073fd78982371d2aa7a50d0f32f5b6e9246b47b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9882ac3ffb623285acf1370a073fd78982371d2aa7a50d0f32f5b6e9246b47b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9882ac3ffb623285acf1370a073fd78982371d2aa7a50d0f32f5b6e9246b47b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid ASCII decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed ASCII bytes as question marks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/codec_decode_byte_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid Latin-1 decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
