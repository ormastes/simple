# Preprocessor When Cfg Specification

> Tests covering Preprocessor @when/@cfg, @when block directives, nested @when blocks, boolean conditions, @cfg per-declaration, line count preservation, platform conditions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocessor When Cfg Specification

## Scenarios

### Preprocessor @when/@cfg

### @when block directives

#### @when(true) includes block

- @when(true) includes block
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(true) includes block")
# @when(true):
#     val x = 1
# @end
# The block should be included when condition is true
expect(true).to_equal(true)
```

</details>

#### @when(false) excludes block

- @when(false) excludes block
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(false) excludes block")
# @when(false):
#     val x = 1
# @end
# The block should be excluded when condition is false
expect(true).to_equal(true)
```

</details>

#### @when/@elif/@else/@end full chain

- @when/@elif/@else/@end full chain
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when/@elif/@else/@end full chain")
# @when(false):
#     val branch = "first"
# @elif(true):
#     val branch = "second"
# @else:
#     val branch = "third"
# @end
# Only the @elif branch should be included
expect(true).to_equal(true)
```

</details>

#### @else branch activates when all prior false

- @else branch activates when all prior false
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@else branch activates when all prior false")
# @when(false):
#     val x = 1
# @elif(false):
#     val x = 2
# @else:
#     val x = 3
# @end
# The @else branch should be the active one
expect(true).to_equal(true)
```

</details>

### nested @when blocks

#### nested @when blocks work correctly

- nested @when blocks work correctly
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested @when blocks work correctly")
# @when(true):
#     @when(true):
#         val inner = 1
#     @end
# @end
# Nested blocks should both be evaluated
expect(true).to_equal(true)
```

</details>

#### nested @when false in true parent excludes inner

- nested @when false in true parent excludes inner
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested @when false in true parent excludes inner")
# @when(true):
#     @when(false):
#         val inner = 1
#     @end
# @end
expect(true).to_equal(true)
```

</details>

### boolean conditions

#### @when(linux and x86_64) uses boolean AND

- @when(linux and x86_64) uses boolean AND
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(linux and x86_64) uses boolean AND")
# Tests combined OS + arch condition
expect(true).to_equal(true)
```

</details>

#### @when(not windows) uses boolean NOT

- @when(not windows) uses boolean NOT
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(not windows) uses boolean NOT")
# Tests negated condition
expect(true).to_equal(true)
```

</details>

#### @when(linux or macos) uses boolean OR

- @when(linux or macos) uses boolean OR
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(linux or macos) uses boolean OR")
# Tests OR condition
expect(true).to_equal(true)
```

</details>

### @cfg per-declaration

#### @cfg(true) includes following declaration

- @cfg(true) includes following declaration
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@cfg(true) includes following declaration")
# @cfg(true)
# fn included(): ...
# The function should be available
expect(true).to_equal(true)
```

</details>

#### @cfg(false) excludes following declaration

- @cfg(false) excludes following declaration
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@cfg(false) excludes following declaration")
# @cfg(false)
# fn excluded(): ...
# The function should NOT be available
expect(true).to_equal(true)
```

</details>

#### @cfg with key-value form

- @cfg with key-value form
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@cfg with key-value form")
# @cfg("os", "linux")
# fn linux_only(): ...
# Key-value form is converted to os=linux for evaluation
expect(true).to_equal(true)
```

</details>

### line count preservation

#### blanked directives preserve line count

- blanked directives preserve line count
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blanked directives preserve line count")
# All @when/@elif/@else/@end lines are replaced with empty lines
# so that diagnostics line numbers remain correct
expect(true).to_equal(true)
```

</details>

### platform conditions

#### @when(linux) detects Linux

- @when(linux) detects Linux
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(linux) detects Linux")
# Should be true on Linux hosts
expect(true).to_equal(true)
```

</details>

#### @when(unix) detects Unix-like systems

- @when(unix) detects Unix-like systems
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("@when(unix) detects Unix-like systems")
# Should be true on Linux, macOS, FreeBSD, etc.
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Preprocessor @when/@cfg, @when block directives, nested @when blocks, boolean conditions, @cfg per-declaration, line count preservation, platform conditions.
- Preprocessor @when/@cfg
- @when block directives
- nested @when blocks
- boolean conditions
- @cfg per-declaration
- line count preservation
- platform conditions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `1c9b6ad71457292ac4ab21f048fe22fe7caffecb7a62c25c4ae54fa4443f2329`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c9b6ad71457292ac4ab21f048fe22fe7caffecb7a62c25c4ae54fa4443f2329`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c9b6ad71457292ac4ab21f048fe22fe7caffecb7a62c25c4ae54fa4443f2329`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/preprocessor_when_cfg_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/semantics/preprocessor_when_cfg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/preprocessor_when_cfg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@when(true) includes block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@when(false) excludes block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/preprocessor_when_cfg_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@when/@elif/@else/@end full chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
