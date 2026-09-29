# Simple Web Engine2d Class Name Multibyte Specification

> Tests covering _first_class_name -- multibyte UTF-8 safety, _collect_class_names -- multibyte UTF-8 safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2d Class Name Multibyte Specification

## Scenarios

### _first_class_name -- multibyte UTF-8 safety

#### extracts a multibyte class token intact (reproduces the bug)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts a multibyte class token intact (reproduces the bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts a multibyte class token intact (reproduces the bug)")
assert_equal(_first_class_name("caf\u{e9} bar"), "caf\u{e9}")
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
assert_equal(_first_class_name("\u{e9}bc def"), "\u{e9}bc")
```

</details>

#### handles multibyte at the last position (single token, no trailing space)

- handles multibyte at the last position (single token, no trailing space)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte at the last position (single token, no trailing space)")
assert_equal(_first_class_name("abc\u{e9}"), "abc\u{e9}")
```

</details>

#### handles multibyte adjacent to the token/space boundary

- handles multibyte adjacent to the token/space boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte adjacent to the token/space boundary")
assert_equal(_first_class_name("x\u{e9} y"), "x\u{e9}")
```

</details>

#### handles a pure-multibyte class value

- handles a pure-multibyte class value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles a pure-multibyte class value")
assert_equal(_first_class_name("\u{e9}\u{e8}\u{ea}"), "\u{e9}\u{e8}\u{ea}")
```

</details>

### _collect_class_names -- multibyte UTF-8 safety

#### collects multiple class tokens including a mixed ASCII+multibyte one

- collects multiple class tokens including a mixed ASCII+multibyte one


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects multiple class tokens including a mixed ASCII+multibyte one")
val names = _collect_class_names("btn caf\u{e9}-icon active")
assert_equal(names[0], "btn")
assert_equal(names[1], "caf\u{e9}-icon")
assert_equal(names[2], "active")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering _first_class_name -- multibyte UTF-8 safety, _collect_class_names -- multibyte UTF-8 safety.
- _first_class_name -- multibyte UTF-8 safety
- _collect_class_names -- multibyte UTF-8 safety

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
- `REQ-BUG-MIXED-INDEX-ENGINE2D-CLASS-NAME`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e6e0a98b8c7ff67e30304cd67a495c152432298c9ed9b29c3de2cb1eddd6aa99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e6e0a98b8c7ff67e30304cd67a495c152432298c9ed9b29c3de2cb1eddd6aa99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e6e0a98b8c7ff67e30304cd67a495c152432298c9ed9b29c3de2cb1eddd6aa99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a multibyte class token intact (reproduces the bug)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multibyte at the first position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_class_name_multibyte_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multibyte at the last position (single token, no trailing space)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
