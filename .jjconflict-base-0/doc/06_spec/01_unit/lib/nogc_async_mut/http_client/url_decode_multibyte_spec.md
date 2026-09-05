# Url Decode Multibyte Specification

> Tests covering url_decode -- multibyte UTF-8 safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Url Decode Multibyte Specification

## Scenarios

### url_decode -- multibyte UTF-8 safety

#### passes a multibyte literal through unchanged (reproduces the bug)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes a multibyte literal through unchanged (reproduces the bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes a multibyte literal through unchanged (reproduces the bug)")
assert_equal(url_decode("caf\u{e9}"), "caf\u{e9}")
```

</details>

#### handles multibyte at the first position

- handles multibyte at the first position


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte at the first position")
assert_equal(url_decode("\u{e9}bc"), "\u{e9}bc")
```

</details>

#### handles multibyte at the last position

- handles multibyte at the last position


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte at the last position")
assert_equal(url_decode("abc\u{e9}"), "abc\u{e9}")
```

</details>

#### handles a pure-multibyte string

- handles a pure-multibyte string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles a pure-multibyte string")
assert_equal(url_decode("\u{e9}\u{e8}\u{ea}"), "\u{e9}\u{e8}\u{ea}")
```

</details>

#### handles mixed ASCII + multibyte + '+'

- handles mixed ASCII + multibyte + '+'


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles mixed ASCII + multibyte + '+'")
assert_equal(url_decode("a+caf\u{e9}+b"), "a caf\u{e9} b")
```

</details>

#### still decodes '+' as space

- still decodes '+' as space


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still decodes '+' as space")
assert_equal(url_decode("a+b"), "a b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering url_decode -- multibyte UTF-8 safety.
- url_decode -- multibyte UTF-8 safety

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
- `REQ-BUG-MIXED-INDEX-URL-DECODE`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eaf0c73bba6015ece29fac9f05ff3d5f3c99869a3219c98dae93875b1c3b63b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eaf0c73bba6015ece29fac9f05ff3d5f3c99869a3219c98dae93875b1c3b63b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eaf0c73bba6015ece29fac9f05ff3d5f3c99869a3219c98dae93875b1c3b63b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes a multibyte literal through unchanged (reproduces the bug)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multibyte at the first position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_client/url_decode_multibyte_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multibyte at the last position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
