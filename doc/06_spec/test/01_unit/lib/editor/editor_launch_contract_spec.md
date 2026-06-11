# Editor Launch Contract Specification

> <details>

<!-- sdn-diagram:id=editor_launch_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_launch_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_launch_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_launch_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Launch Contract Specification

## Scenarios

### editor launch contract

#### parses TUI, GUI, and files in shared lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui = editor_launch_parse(["--tui", "a.md", "b.spl"])
expect(tui.mode).to_equal("tui")
expect(tui.files.len()).to_equal(2)
expect(tui.unknown_option).to_equal("")

val gui = editor_launch_parse(["--gui", "a.md"])
expect(gui.mode).to_equal("gui")
expect(gui.files.len()).to_equal(1)

val sdl = editor_launch_parse(["--gui-sdl"])
expect(sdl.mode).to_equal("gui-sdl")
```

</details>

#### filters log options before app entrypoints parse editor options

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleaned = editor_launch_clean_log_args(["--json", "--progress", "dots", "--gui", "note.md"])
expect(cleaned.len()).to_equal(2)
expect(cleaned[0]).to_equal("--gui")
expect(cleaned[1]).to_equal("note.md")
```

</details>

#### shares launch parsing between editor, IDE, and examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ide = read_text("src/app/ide/main.spl")
val editor = read_text("src/app/editor/main.spl")
val tui = read_text("src/app/editor/tui_main.spl")
val example = read_text("examples/10_tooling/ide/simple_ide_launch.spl")
val render_example = read_text("examples/10_tooling/ide/simple_ide_render.spl")

expect(ide.contains("editor_launch_parse")).to_equal(true)
expect(editor.contains("editor_launch_mode")).to_equal(true)
expect(tui.contains("editor_launch_file_args_after_command")).to_equal(true)
expect(example.contains("std.editor.core.launch")).to_equal(true)
expect(render_example.contains("std.editor.backend.gui_backend")).to_equal(true)
expect(render_example.contains("common.ui.web_render_api")).to_equal(true)
```

</details>

#### runs the IDE and example launch entrypoints through bin/simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ide_result = process_run("bin/simple", ["run", "src/app/ide/main.spl", "--gui", "README.md"])
expect(ide_result.2).to_equal(0)
expect(ide_result.0).to_contain("Simple IDE v0.1.0")
expect(ide_result.0).to_contain("Ready for gui IDE startup with 1 file(s).")

val example_result = process_run("bin/simple", ["run", "examples/10_tooling/ide/simple_ide_launch.spl"])
expect(example_result.2).to_equal(0)
expect(example_result.0).to_contain("mode=tui")
expect(example_result.0).to_contain("files=2")
```

</details>

#### runs the embedded example IDE render entrypoint through bin/simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render_result = process_run("bin/simple", ["run", "examples/10_tooling/ide/simple_ide_render.spl"])
expect(render_result.2).to_equal(0)
expect(render_result.0).to_contain("target=pure_simple")
expect(render_result.0).to_contain("has_editor_source=true")
expect(render_result.0).to_contain("has_markdown_language=true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/editor_launch_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor launch contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
