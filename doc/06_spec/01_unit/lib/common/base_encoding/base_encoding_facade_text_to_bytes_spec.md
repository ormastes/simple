# Base Encoding Facade Text To Bytes Specification

> Tests covering base encoding facade text_to_bytes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base Encoding Facade Text To Bytes Specification

## Scenarios

### base encoding facade text_to_bytes

#### encodes ASCII unchanged

- encodes ASCII unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes ASCII unchanged")
assert_equal(byte_list(text_to_bytes("Hi")), "72,105")
```

</details>

#### encodes a two-byte codepoint as C3 A9

- encodes a two-byte codepoint as C3 A9


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a two-byte codepoint as C3 A9")
assert_equal(byte_list(text_to_bytes("é")), "195,169")
```

</details>

#### encodes a three-byte codepoint as E2 82 AC

- encodes a three-byte codepoint as E2 82 AC


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a three-byte codepoint as E2 82 AC")
assert_equal(byte_list(text_to_bytes("€")), "226,130,172")
```

</details>

#### encodes a four-byte codepoint as F0 9F 98 80

- encodes a four-byte codepoint as F0 9F 98 80


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a four-byte codepoint as F0 9F 98 80")
assert_equal(byte_list(text_to_bytes("😀")), "240,159,152,128")
```

</details>

#### round-trips mixed-width text through bytes_to_text

- round-trips mixed-width text through bytes_to_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips mixed-width text through bytes_to_text")
val s = "aé€😀z"
assert_equal(bytes_to_text(text_to_bytes(s)), s)
```

</details>

#### emits no trailing padding bytes for multi-byte input

- emits no trailing padding bytes for multi-byte input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits no trailing padding bytes for multi-byte input")
assert_equal(text_to_bytes("aé€😀z").len(), 11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering base encoding facade text_to_bytes.
- base encoding facade text_to_bytes

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d84bc4eec926c134399c056c37a21370baa4ef53578265cbefbe1a11daf2cfbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d84bc4eec926c134399c056c37a21370baa4ef53578265cbefbe1a11daf2cfbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d84bc4eec926c134399c056c37a21370baa4ef53578265cbefbe1a11daf2cfbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.spl
mirror: doc/06_spec/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes ASCII unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes a two-byte codepoint as C3 A9' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/base_encoding/base_encoding_facade_text_to_bytes_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes a three-byte codepoint as E2 82 AC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
