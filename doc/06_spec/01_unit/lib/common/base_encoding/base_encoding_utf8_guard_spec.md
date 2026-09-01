# Base Encoding Utf8 Guard Specification

> Tests covering base encoding UTF-8 byte guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base Encoding Utf8 Guard Specification

## Scenarios

### base encoding UTF-8 byte guards

#### keeps valid multi-byte UTF-8

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid multi-byte UTF-8


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid multi-byte UTF-8")
assert_equal(bytes_to_text([0xC3, 0xA9]), "é")
```

</details>

#### rejects invalid continuation bytes

- rejects invalid continuation bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid continuation bytes")
assert_equal(bytes_to_text([0xC3, 0x41]), "?A")
```

</details>

#### rejects overlong encodings

- rejects overlong encodings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlong encodings")
assert_equal(bytes_to_text([0xC0, 0xAF]), "??")
```

</details>

#### rejects surrogate codepoints

- rejects surrogate codepoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects surrogate codepoints")
assert_equal(bytes_to_text([0xED, 0xA0, 0x80]), "???")
```

</details>

#### rejects out-of-range leading bytes

- rejects out-of-range leading bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects out-of-range leading bytes")
assert_equal(bytes_to_text([0xFF, 0xBF, 0xBF, 0xBF]), "????")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base encoding UTF-8 byte guards.
- base encoding UTF-8 byte guards

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

- Canonical SPipe generation for source `b4a83efcd9195442bf17b42468138a47f785b5f78d990dfb0f0ef4ea01d3faca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4a83efcd9195442bf17b42468138a47f785b5f78d990dfb0f0ef4ea01d3faca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4a83efcd9195442bf17b42468138a47f785b5f78d990dfb0f0ef4ea01d3faca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid multi-byte UTF-8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid continuation bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overlong encodings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
