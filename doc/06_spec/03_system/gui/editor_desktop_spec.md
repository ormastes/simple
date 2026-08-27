# Editor Desktop Specification

> Tests covering desktop_commands — dialog functions, desktop_commands — clipboard functions, commands.spl — desktop dispatch, commands.spl — commandline parsing, commands.spl — palette entries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Desktop Specification

## Scenarios

### desktop_commands — dialog functions

#### defines editor_open_file_dialog returning text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines editor_open_file_dialog returning text
   - Expected: src contains `fn editor_open_file_dialog() -> text:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_open_file_dialog returning text")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_open_file_dialog() -> text:")).to_equal(true)
```

</details>

#### defines editor_save_file_dialog returning text

- defines editor_save_file_dialog returning text
   - Expected: src contains `fn editor_save_file_dialog() -> text:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_save_file_dialog returning text")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_save_file_dialog() -> text:")).to_equal(true)
```

</details>

#### calls open_file_dialog with options

- calls open_file_dialog with options
   - Expected: src contains `open_file_dialog(opts)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls open_file_dialog with options")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("open_file_dialog(opts)")).to_equal(true)
```

</details>

#### calls save_file_dialog with options

- calls save_file_dialog with options
   - Expected: src contains `save_file_dialog(opts)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls save_file_dialog with options")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("save_file_dialog(opts)")).to_equal(true)
```

</details>

### desktop_commands — clipboard functions

#### defines editor_clipboard_copy accepting text returning bool

- defines editor_clipboard_copy accepting text returning bool
   - Expected: src contains `fn editor_clipboard_copy(content: text) -> bool:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_clipboard_copy accepting text returning bool")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_clipboard_copy(content: text) -> bool:")).to_equal(true)
```

</details>

#### defines editor_clipboard_paste returning text

- defines editor_clipboard_paste returning text
   - Expected: src contains `fn editor_clipboard_paste() -> text:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_clipboard_paste returning text")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_clipboard_paste() -> text:")).to_equal(true)
```

</details>

#### defines editor_clipboard_cut accepting text returning bool

- defines editor_clipboard_cut accepting text returning bool
   - Expected: src contains `fn editor_clipboard_cut(content: text) -> bool:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_clipboard_cut accepting text returning bool")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_clipboard_cut(content: text) -> bool:")).to_equal(true)
```

</details>

#### calls clipboard_write for copy

- calls clipboard_write for copy
   - Expected: src contains `clipboard_write(content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls clipboard_write for copy")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("clipboard_write(content)")).to_equal(true)
```

</details>

#### calls clipboard_read for paste

- calls clipboard_read for paste
   - Expected: src contains `clipboard_read()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls clipboard_read for paste")
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("clipboard_read()")).to_equal(true)
```

</details>

### commands.spl — desktop dispatch

#### dispatches open-dialog command

- dispatches open-dialog command
   - Expected: src contains `"open-dialog":`
   - Expected: src contains `editor_open_file_dialog()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches open-dialog command")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"open-dialog\":")).to_equal(true)
expect(src.contains("editor_open_file_dialog()")).to_equal(true)
```

</details>

#### dispatches save-dialog command

- dispatches save-dialog command
   - Expected: src contains `"save-dialog":`
   - Expected: src contains `editor_save_file_dialog()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches save-dialog command")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"save-dialog\":")).to_equal(true)
expect(src.contains("editor_save_file_dialog()")).to_equal(true)
```

</details>

#### dispatches clipboard-copy command

- dispatches clipboard-copy command
   - Expected: src contains `"clipboard-copy":`
   - Expected: src contains `editor_clipboard_copy(line_cc)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches clipboard-copy command")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"clipboard-copy\":")).to_equal(true)
expect(src.contains("editor_clipboard_copy(line_cc)")).to_equal(true)
```

</details>

#### dispatches clipboard-paste command

- dispatches clipboard-paste command
   - Expected: src contains `"clipboard-paste":`
   - Expected: src contains `editor_clipboard_paste()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches clipboard-paste command")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"clipboard-paste\":")).to_equal(true)
expect(src.contains("editor_clipboard_paste()")).to_equal(true)
```

</details>

### commands.spl — commandline parsing

#### parses open as open-dialog

- parses open as open-dialog
   - Expected: src contains `trimmed == "open"`
   - Expected: src contains `editor_cmd("open-dialog")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses open as open-dialog")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("trimmed == \"open\"")).to_equal(true)
expect(src.contains("editor_cmd(\"open-dialog\")")).to_equal(true)
```

</details>

#### parses saveas as save-dialog

- parses saveas as save-dialog
   - Expected: src contains `trimmed == "saveas"`
   - Expected: src contains `editor_cmd("save-dialog")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses saveas as save-dialog")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("trimmed == \"saveas\"")).to_equal(true)
expect(src.contains("editor_cmd(\"save-dialog\")")).to_equal(true)
```

</details>

### commands.spl — palette entries

#### has Open Dialog palette entry

- has Open Dialog palette entry
   - Expected: src contains `name: "Open Dialog"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Open Dialog palette entry")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Open Dialog\"")).to_equal(true)
```

</details>

#### has Save As Dialog palette entry

- has Save As Dialog palette entry
   - Expected: src contains `name: "Save As Dialog"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Save As Dialog palette entry")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Save As Dialog\"")).to_equal(true)
```

</details>

#### has Copy palette entry

- has Copy palette entry
   - Expected: src contains `name: "Copy"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Copy palette entry")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Copy\"")).to_equal(true)
```

</details>

#### has Paste palette entry

- has Paste palette entry
   - Expected: src contains `name: "Paste"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Paste palette entry")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Paste\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_desktop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering desktop_commands — dialog functions, desktop_commands — clipboard functions, commands.spl — desktop dispatch, commands.spl — commandline parsing, commands.spl — palette entries.
- desktop_commands — dialog functions
- desktop_commands — clipboard functions
- commands.spl — desktop dispatch
- commands.spl — commandline parsing
- commands.spl — palette entries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `45b083471e069366d098c26b457e8285cbf3fe97e37beda58b6bd5d102538edc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45b083471e069366d098c26b457e8285cbf3fe97e37beda58b6bd5d102538edc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45b083471e069366d098c26b457e8285cbf3fe97e37beda58b6bd5d102538edc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_desktop_spec.spl
mirror: doc/06_spec/03_system/gui/editor_desktop_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_desktop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_desktop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_desktop_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines editor_open_file_dialog returning text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_desktop_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines editor_save_file_dialog returning text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_desktop_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls open_file_dialog with options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
