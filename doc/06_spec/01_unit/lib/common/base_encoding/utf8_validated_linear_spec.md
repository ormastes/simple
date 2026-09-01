# Utf8 Validated Linear Specification

> Tests covering linear validated UTF-8 owner facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf8 Validated Linear Specification

## Scenarios

### linear validated UTF-8 owner facade

#### accepts ASCII including NUL and DEL

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts ASCII including NUL and DEL


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts ASCII including NUL and DEL")
_expect_utf8_success([0u8, 65u8, 127u8])
```

</details>

#### accepts two-byte lower and upper boundaries

- accepts two-byte lower and upper boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts two-byte lower and upper boundaries")
_expect_utf8_success([0xC2u8, 0x80u8, 0xDFu8, 0xBFu8])
```

</details>

#### accepts three-byte lower and upper boundaries

- accepts three-byte lower and upper boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts three-byte lower and upper boundaries")
_expect_utf8_success([0xE0u8, 0xA0u8, 0x80u8, 0xEFu8, 0xBFu8, 0xBFu8])
```

</details>

#### accepts four-byte lower and upper boundaries

- accepts four-byte lower and upper boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts four-byte lower and upper boundaries")
_expect_utf8_success([0xF0u8, 0x90u8, 0x80u8, 0x80u8, 0xF4u8, 0x8Fu8, 0xBFu8, 0xBFu8])
```

</details>

#### rejects C0 C1 and F5 invalid leading bytes

- rejects C0 C1 and F5 invalid leading bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects C0 C1 and F5 invalid leading bytes")
_expect_utf8_error([0xC0u8, 0x80u8], "invalid leading byte")
_expect_utf8_error([0xC1u8, 0xBFu8], "invalid leading byte")
_expect_utf8_error([0xF5u8, 0x80u8, 0x80u8, 0x80u8], "invalid leading byte")
```

</details>

#### rejects overlong surrogate and out-of-range special sequences

- rejects overlong surrogate and out-of-range special sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlong surrogate and out-of-range special sequences")
_expect_utf8_error([0xE0u8, 0x9Fu8, 0xBFu8], "overlong three-byte sequence")
_expect_utf8_error([0xEDu8, 0xA0u8, 0x80u8], "surrogate code point")
_expect_utf8_error([0xF0u8, 0x8Fu8, 0xBFu8, 0xBFu8], "overlong four-byte sequence")
_expect_utf8_error([0xF4u8, 0x90u8, 0x80u8, 0x80u8], "code point exceeds U+10FFFF")
```

</details>

#### rejects two three and four-byte truncation

- rejects two three and four-byte truncation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects two three and four-byte truncation")
_expect_utf8_error([0xC2u8], "truncated two-byte sequence")
_expect_utf8_error([0xE1u8, 0x80u8], "truncated three-byte sequence")
_expect_utf8_error([0xF1u8, 0x80u8, 0x80u8], "truncated four-byte sequence")
```

</details>

#### classifies bad second continuation before special range errors

- classifies bad second continuation before special range errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies bad second continuation before special range errors")
_expect_utf8_error([0xE0u8, 0x41u8, 0x80u8], "malformed three-byte sequence")
_expect_utf8_error([0xEDu8, 0x41u8, 0x80u8], "malformed three-byte sequence")
_expect_utf8_error([0xF0u8, 0x41u8, 0x80u8, 0x80u8], "malformed four-byte sequence")
_expect_utf8_error([0xF4u8, 0x41u8, 0x80u8, 0x80u8], "malformed four-byte sequence")
```

</details>

#### rejects bad ordinary second third and fourth continuations

- rejects bad ordinary second third and fourth continuations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bad ordinary second third and fourth continuations")
_expect_utf8_error([0xC2u8, 0x41u8], "malformed two-byte sequence")
_expect_utf8_error([0xE1u8, 0x41u8, 0x80u8], "malformed three-byte sequence")
_expect_utf8_error([0xE1u8, 0x80u8, 0x41u8], "malformed three-byte sequence")
_expect_utf8_error([0xF1u8, 0x41u8, 0x80u8, 0x80u8], "malformed four-byte sequence")
_expect_utf8_error([0xF1u8, 0x80u8, 0x41u8, 0x80u8], "malformed four-byte sequence")
_expect_utf8_error([0xF1u8, 0x80u8, 0x80u8, 0x41u8], "malformed four-byte sequence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering linear validated UTF-8 owner facade.
- linear validated UTF-8 owner facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `101d2ccb07fa16bcde4ac1b9606267c188b1e00b69e97187719d69e8d85e0231`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `101d2ccb07fa16bcde4ac1b9606267c188b1e00b69e97187719d69e8d85e0231`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `101d2ccb07fa16bcde4ac1b9606267c188b1e00b69e97187719d69e8d85e0231`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts ASCII including NUL and DEL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts two-byte lower and upper boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/utf8_validated_linear_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts three-byte lower and upper boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
