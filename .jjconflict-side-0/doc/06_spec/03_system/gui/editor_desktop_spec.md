# Editor Desktop Specification

> <details>

<!-- sdn-diagram:id=editor_desktop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_desktop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_desktop_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_desktop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Desktop Specification

## Scenarios

### desktop_commands — dialog functions

#### defines editor_open_file_dialog returning text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_open_file_dialog() -> text:")).to_equal(true)
```

</details>

#### defines editor_save_file_dialog returning text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_save_file_dialog() -> text:")).to_equal(true)
```

</details>

#### calls open_file_dialog with options

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("open_file_dialog(opts)")).to_equal(true)
```

</details>

#### calls save_file_dialog with options

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("save_file_dialog(opts)")).to_equal(true)
```

</details>

### desktop_commands — clipboard functions

#### defines editor_clipboard_copy accepting text returning bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_clipboard_copy(content: text) -> bool:")).to_equal(true)
```

</details>

#### defines editor_clipboard_paste returning text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_clipboard_paste() -> text:")).to_equal(true)
```

</details>

#### defines editor_clipboard_cut accepting text returning bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("fn editor_clipboard_cut(content: text) -> bool:")).to_equal(true)
```

</details>

#### calls clipboard_write for copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("clipboard_write(content)")).to_equal(true)
```

</details>

#### calls clipboard_read for paste

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/desktop_commands.spl")
expect(src.contains("clipboard_read()")).to_equal(true)
```

</details>

### commands.spl — desktop dispatch

#### dispatches open-dialog command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"open-dialog\":")).to_equal(true)
expect(src.contains("editor_open_file_dialog()")).to_equal(true)
```

</details>

#### dispatches save-dialog command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"save-dialog\":")).to_equal(true)
expect(src.contains("editor_save_file_dialog()")).to_equal(true)
```

</details>

#### dispatches clipboard-copy command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"clipboard-copy\":")).to_equal(true)
expect(src.contains("editor_clipboard_copy(line_cc)")).to_equal(true)
```

</details>

#### dispatches clipboard-paste command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"clipboard-paste\":")).to_equal(true)
expect(src.contains("editor_clipboard_paste()")).to_equal(true)
```

</details>

### commands.spl — commandline parsing

#### parses open as open-dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("trimmed == \"open\"")).to_equal(true)
expect(src.contains("editor_cmd(\"open-dialog\")")).to_equal(true)
```

</details>

#### parses saveas as save-dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("trimmed == \"saveas\"")).to_equal(true)
expect(src.contains("editor_cmd(\"save-dialog\")")).to_equal(true)
```

</details>

### commands.spl — palette entries

#### has Open Dialog palette entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Open Dialog\"")).to_equal(true)
```

</details>

#### has Save As Dialog palette entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Save As Dialog\"")).to_equal(true)
```

</details>

#### has Copy palette entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("name: \"Copy\"")).to_equal(true)
```

</details>

#### has Paste palette entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
