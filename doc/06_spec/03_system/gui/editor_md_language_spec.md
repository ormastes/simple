# Editor Md Language Specification

> Tests covering md language — structs, md language — function signatures, md language — diagnose logic, md language — completion logic, md language — hover logic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Md Language Specification

## Scenarios

### md language — structs

#### defines MdDiagnostic with line, col, message, severity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines MdDiagnostic with line, col, message, severity
   - Expected: src contains `struct MdDiagnostic:`
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
step("defines MdDiagnostic with line, col, message, severity")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("struct MdDiagnostic:")).to_equal(true)
expect(src.contains("line: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("severity: text")).to_equal(true)
```

</details>

#### defines MdCompletion with label, kind, detail

- defines MdCompletion with label, kind, detail
   - Expected: src contains `struct MdCompletion:`
   - Expected: src contains `label: text`
   - Expected: src contains `kind: text`
   - Expected: src contains `detail: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines MdCompletion with label, kind, detail")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("struct MdCompletion:")).to_equal(true)
expect(src.contains("label: text")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("detail: text")).to_equal(true)
```

</details>

### md language — function signatures

#### defines md_language_diagnose returning [MdDiagnostic]

- defines md_language_diagnose returning [MdDiagnostic]
   - Expected: src contains `fn md_language_diagnose(content: text) -> [MdDiagnostic]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines md_language_diagnose returning [MdDiagnostic]")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_diagnose(content: text) -> [MdDiagnostic]")).to_equal(true)
```

</details>

#### defines md_language_complete returning [MdCompletion]

- defines md_language_complete returning [MdCompletion]
   - Expected: src contains `fn md_language_complete(content: text, line: i64, col: i64) -> [MdCompletion]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines md_language_complete returning [MdCompletion]")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_complete(content: text, line: i64, col: i64) -> [MdCompletion]")).to_equal(true)
```

</details>

#### defines md_language_hover returning text

- defines md_language_hover returning text
   - Expected: src contains `fn md_language_hover(content: text, line: i64, col: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines md_language_hover returning text")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_hover(content: text, line: i64, col: i64) -> text")).to_equal(true)
```

</details>

### md language — diagnose logic

#### checks heading-space with a byte slice after the '#' run

- checks heading-space with a byte slice after the '#' run
   - Expected: src contains `if hashes < trimmed.len() and trimmed[hashes:hashes + 1] != " ":`
   - Expected: src contains `"#"`
   - Expected: src contains `Heading requires a space after '#'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks heading-space with a byte slice after the '#' run")
# STALE-SPEC REPOINT (2026-08-10): this asserted `char_at`, which the
# implementation no longer uses — it now byte-slices, deliberately, to
# avoid the character/byte-index mismatch. The only remaining `char_at`
# in the file is the comment recording that change, so the assertion
# could not fail. Repointed at the byte-slice check that replaced it.
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("if hashes < trimmed.len() and trimmed[hashes:hashes + 1] != \" \":")).to_equal(true)
expect(src.contains("\"#\"")).to_equal(true)
expect(src.contains("Heading requires a space after '#'")).to_equal(true)
```

</details>

#### detects empty links using contains ']()'

- detects empty links using contains ']()'
   - Expected: src contains `"["`
   - Expected: src contains `contains("]()")`
   - Expected: src contains `Empty link target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects empty links using contains ']()'")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("\"[\"")).to_equal(true)
expect(src.contains("contains(\"]()\")")).to_equal(true)
expect(src.contains("Empty link target")).to_equal(true)
```

</details>

#### counts code fences using starts_with triple backtick

- counts code fences using starts_with triple backtick
   - Expected: src contains `starts_with("```")`
   - Expected: src contains `fence_count`
   - Expected: src contains `fence_count % 2 != 0`
   - Expected: src contains `Unclosed code fence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts code fences using starts_with triple backtick")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("starts_with(\"```\")")).to_equal(true)
expect(src.contains("fence_count")).to_equal(true)
expect(src.contains("fence_count % 2 != 0")).to_equal(true)
expect(src.contains("Unclosed code fence")).to_equal(true)
```

</details>

#### checks trailing whitespace

- checks trailing whitespace
   - Expected: src contains `Trailing whitespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks trailing whitespace")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("Trailing whitespace")).to_equal(true)
```

</details>

### md language — completion logic

#### suggests heading levels after #

- suggests heading levels after #
   - Expected: src contains `Heading level 2`
   - Expected: src contains `Heading level 3`
   - Expected: src contains `"## "`
   - Expected: src contains `"### "`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests heading levels after #")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("Heading level 2")).to_equal(true)
expect(src.contains("Heading level 3")).to_equal(true)
expect(src.contains("\"## \"")).to_equal(true)
expect(src.contains("\"### \"")).to_equal(true)
```

</details>

#### suggests link template after [

- suggests link template after [
   - Expected: src contains `ends_with("[")`
   - Expected: src contains `[text](url)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests link template after [")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("ends_with(\"[\")")).to_equal(true)
expect(src.contains("[text](url)")).to_equal(true)
```

</details>

#### suggests common languages after triple backtick

- suggests common languages after triple backtick
   - Expected: src contains `"simple"`
   - Expected: src contains `"bash"`
   - Expected: src contains `"json"`
   - Expected: src contains `"python"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("suggests common languages after triple backtick")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("\"simple\"")).to_equal(true)
expect(src.contains("\"bash\"")).to_equal(true)
expect(src.contains("\"json\"")).to_equal(true)
expect(src.contains("\"python\"")).to_equal(true)
```

</details>

### md language — hover logic

#### returns heading level string for heading lines

- returns heading level string for heading lines
   - Expected: src contains `Heading level `
   - Expected: src contains `_md_heading_level`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns heading level string for heading lines")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("Heading level ")).to_equal(true)
expect(src.contains("_md_heading_level")).to_equal(true)
```

</details>

#### returns language name for code fence lines

- returns language name for code fence lines
   - Expected: src contains `starts_with("```")`
   - Expected: src contains `trimmed.slice(3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns language name for code fence lines")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("starts_with(\"```\")")).to_equal(true)
expect(src.contains("trimmed.slice(3")).to_equal(true)
```

</details>

#### returns URL when cursor is on a link

- returns URL when cursor is on a link
   - Expected: src contains `_md_find_link_url`
   - Expected: src contains `fn _md_find_link_url(line: text, col: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns URL when cursor is on a link")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("_md_find_link_url")).to_equal(true)
expect(src.contains("fn _md_find_link_url(line: text, col: i64) -> text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_md_language_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering md language — structs, md language — function signatures, md language — diagnose logic, md language — completion logic, md language — hover logic.
- md language — structs
- md language — function signatures
- md language — diagnose logic
- md language — completion logic
- md language — hover logic

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9540edf2dc42b8e9501b20c635599952feb24a4f2def3cad9f4ffbee51351e62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9540edf2dc42b8e9501b20c635599952feb24a4f2def3cad9f4ffbee51351e62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9540edf2dc42b8e9501b20c635599952feb24a4f2def3cad9f4ffbee51351e62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_md_language_spec.spl
mirror: doc/06_spec/03_system/gui/editor_md_language_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_md_language_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_md_language_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_md_language_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines MdDiagnostic with line, col, message, severity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_md_language_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines MdCompletion with label, kind, detail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_md_language_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines md_language_diagnose returning [MdDiagnostic]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
