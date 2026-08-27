# Editor Spl Language Specification

> Tests covering editor spl language — structs, editor spl language — diagnose, editor spl language — complete, editor spl language — hover.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Spl Language Specification

## Scenarios

### editor spl language — structs

#### defines SplDiagnostic struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines SplDiagnostic struct
   - Expected: src contains `struct SplDiagnostic:`
   - Expected: src contains `line: i64`
   - Expected: src contains `col: i64`
   - Expected: src contains `message: text`
   - Expected: src contains `severity: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SplDiagnostic struct")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("struct SplDiagnostic:")).to_equal(true)
expect(src.contains("line: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("severity: text")).to_equal(true)
```

</details>

#### defines SplCompletion struct

- defines SplCompletion struct
   - Expected: src contains `struct SplCompletion:`
   - Expected: src contains `label: text`
   - Expected: src contains `kind: text`
   - Expected: src contains `detail: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SplCompletion struct")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("struct SplCompletion:")).to_equal(true)
expect(src.contains("label: text")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("detail: text")).to_equal(true)
```

</details>

### editor spl language — diagnose

#### has spl_language_diagnose function

- has spl_language_diagnose function
   - Expected: src contains `fn spl_language_diagnose(content: text) -> [SplDiagnostic]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has spl_language_diagnose function")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_diagnose(content: text) -> [SplDiagnostic]")).to_equal(true)
```

</details>

#### detects tab character

- detects tab character
   - Expected: src contains `Tab character found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects tab character")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Tab character found")).to_equal(true)
```

</details>

#### detects trailing whitespace

- detects trailing whitespace
   - Expected: src contains `Trailing whitespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects trailing whitespace")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Trailing whitespace")).to_equal(true)
```

</details>

#### detects unclosed string literal

- detects unclosed string literal
   - Expected: src contains `unclosed string literal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects unclosed string literal")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("unclosed string literal")).to_equal(true)
```

</details>

#### detects missing colon on fn/me signature

- detects missing colon on fn/me signature
   - Expected: src contains `missing ':'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects missing colon on fn/me signature")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("missing ':'")).to_equal(true)
```

</details>

#### suggests val over var hint

- suggests val over var hint
   - Expected: src contains `'val'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests val over var hint")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("'val'")).to_equal(true)
```

</details>

### editor spl language — complete

#### has spl_language_complete function

- has spl_language_complete function
   - Expected: src contains `fn spl_language_complete(content: text, line: i64, col: i64) -> [SplCompletion]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has spl_language_complete function")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_complete(content: text, line: i64, col: i64) -> [SplCompletion]")).to_equal(true)
```

</details>

#### includes fn keyword completion

- includes fn keyword completion
   - Expected: src contains `"fn"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes fn keyword completion")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"fn\"")).to_equal(true)
```

</details>

#### includes val keyword completion

- includes val keyword completion
   - Expected: src contains `"val"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes val keyword completion")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"val\"")).to_equal(true)
```

</details>

#### includes var keyword completion

- includes var keyword completion
   - Expected: src contains `"var"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes var keyword completion")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"var\"")).to_equal(true)
```

</details>

#### suggests std. prefix after use

- suggests std. prefix after use
   - Expected: src contains `"std."`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests std. prefix after use")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"std.\"")).to_equal(true)
```

</details>

#### uses kind=keyword for keywords

- uses kind=keyword for keywords
   - Expected: src contains `"keyword"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses kind=keyword for keywords")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"keyword\"")).to_equal(true)
```

</details>

#### uses kind=snippet for snippets

- uses kind=snippet for snippets
   - Expected: src contains `"snippet"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses kind=snippet for snippets")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"snippet\"")).to_equal(true)
```

</details>

### editor spl language — hover

#### has spl_language_hover function

- has spl_language_hover function
   - Expected: src contains `fn spl_language_hover(content: text, line: i64, col: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has spl_language_hover function")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_hover(content: text, line: i64, col: i64) -> text")).to_equal(true)
```

</details>

#### describes val keyword

- describes val keyword
   - Expected: src contains `Immutable binding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("describes val keyword")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Immutable binding")).to_equal(true)
```

</details>

#### describes me keyword

- describes me keyword
   - Expected: src contains `Mutable method (modifies self)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("describes me keyword")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Mutable method (modifies self)")).to_equal(true)
```

</details>

#### describes fn keyword

- describes fn keyword
   - Expected: src contains `Immutable method or free function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("describes fn keyword")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Immutable method or free function")).to_equal(true)
```

</details>

#### describes extern keyword

- describes extern keyword
   - Expected: src contains `Runtime-provided function declaration`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("describes extern keyword")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Runtime-provided function declaration")).to_equal(true)
```

</details>

#### returns empty string for unknown word

- returns empty string for unknown word
   - Expected: src contains `return ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for unknown word")
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("return \"\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_spl_language_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor spl language — structs, editor spl language — diagnose, editor spl language — complete, editor spl language — hover.
- editor spl language — structs
- editor spl language — diagnose
- editor spl language — complete
- editor spl language — hover

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc15949fce7c242bc7ec10b82f467bc20716fb99228060f371c9053ae1452b2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc15949fce7c242bc7ec10b82f467bc20716fb99228060f371c9053ae1452b2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc15949fce7c242bc7ec10b82f467bc20716fb99228060f371c9053ae1452b2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_spl_language_spec.spl
mirror: doc/06_spec/03_system/gui/editor_spl_language_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_spl_language_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_spl_language_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_spl_language_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SplDiagnostic struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_spl_language_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SplCompletion struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_spl_language_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has spl_language_diagnose function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
