# Md Lsp Extract Field Multibyte Specification

> Tests covering _md_lsp_extract_field -- multibyte UTF-8 safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Lsp Extract Field Multibyte Specification

## Scenarios

### _md_lsp_extract_field -- multibyte UTF-8 safety

#### extracts a string value containing a multibyte char

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts a string value containing a multibyte char


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a string value containing a multibyte char")
val json = "{\"name\":\"caf\u{e9}\"}"
assert_equal(_md_lsp_extract_field(json, "name"), "caf\u{e9}")
```

</details>

#### extracts a nested object containing several multibyte codepoints (reproduces the bug)

- extracts a nested object containing several multibyte codepoints (reproduces the bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a nested object containing several multibyte codepoints (reproduces the bug)")
val json = "{\"params\":{\"name\":\"caf\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\"},\"id\":1}"
assert_equal(
    _md_lsp_extract_field(json, "params"),
    "{\"name\":\"caf\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\u{e9}\"}"
)
```

</details>

#### extracts a nested array containing a multibyte string element

- extracts a nested array containing a multibyte string element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a nested array containing a multibyte string element")
val json = "{\"items\":[\"caf\u{e9}\",\"b\"],\"id\":2}"
assert_equal(_md_lsp_extract_field(json, "items"), "[\"caf\u{e9}\",\"b\"]")
```

</details>

#### extracts a plain ASCII number field unaffected

- extracts a plain ASCII number field unaffected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a plain ASCII number field unaffected")
val json = "{\"id\":42}"
assert_equal(_md_lsp_extract_field(json, "id"), "42")
```

</details>

#### extracts a purely-multibyte string value

- extracts a purely-multibyte string value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("extracts a purely-multibyte string value")
val json = "{\"name\":\"\u{e9}\u{e8}\u{ea}\"}"
assert_equal(_md_lsp_extract_field(json, "name"), "\u{e9}\u{e8}\u{ea}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering _md_lsp_extract_field -- multibyte UTF-8 safety.
- _md_lsp_extract_field -- multibyte UTF-8 safety

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
- `REQ-BUG-MIXED-INDEX-MD-LSP-EXTRACT-FIELD`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33ad8cacb9e6b02331508227ffc06e0d68ce0822f58bc25d0653238358b7ad8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33ad8cacb9e6b02331508227ffc06e0d68ce0822f58bc25d0653238358b7ad8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33ad8cacb9e6b02331508227ffc06e0d68ce0822f58bc25d0653238358b7ad8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl
mirror: doc/06_spec/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a string value containing a multibyte char' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a nested object containing several multibyte codepoints (reproduces the bug)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/md_lsp/md_lsp_extract_field_multibyte_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a nested array containing a multibyte string element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
