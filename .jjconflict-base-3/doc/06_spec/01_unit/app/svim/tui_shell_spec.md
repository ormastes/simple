# Tui Shell Specification

> 1. expect help contains

<!-- sdn-diagram:id=tui_shell_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_shell_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_shell_spec -> std
tui_shell_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_shell_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Shell Specification

## Scenarios

### svim host shell helpers

#### renders help text with shared and host commands

1. expect help contains
2. expect help contains
3. expect help contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = svim_shell_help_text()
expect help.contains(":w <path>") to_equal true
expect help.contains("open <path>") to_equal true
expect help.contains(".buffers") to_equal true
```

</details>

#### formats pending prompts for open save and search flows

1. expect svim shell prompt
2. expect svim shell prompt
3. expect svim shell prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = SvimSession.new()
expect svim_shell_prompt(session, "open-buffer") to_equal "open path> "
expect svim_shell_prompt(session, "save-as") to_equal "write path> "
expect svim_shell_prompt(session, "search-forward") to_equal "search> "
```

</details>

#### classifies host aliases and shell meta commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open_cmd = svim_shell_classify_line(SvimMode.Normal, "open /tmp/demo.txt")
expect open_cmd.0 to_equal "dispatch"
expect open_cmd.1 to_equal "open-buffer:/tmp/demo.txt"
val write_cmd = svim_shell_classify_line(SvimMode.Normal, "write /tmp/demo.txt")
expect write_cmd.0 to_equal "dispatch"
expect write_cmd.1 to_equal "save-as:/tmp/demo.txt"
val buffers_cmd = svim_shell_classify_line(SvimMode.Normal, ".buffers")
expect buffers_cmd.0 to_equal "buffers"
expect buffers_cmd.1 to_equal ""
```

</details>

#### routes insert mode text and shell escapes distinctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insert_text = svim_shell_classify_line(SvimMode.Insert, "hello")
expect insert_text.0 to_equal "insert"
expect insert_text.1 to_equal "hello"
val insert_escape = svim_shell_classify_line(SvimMode.Insert, ".esc")
expect insert_escape.0 to_equal "dispatch"
expect insert_escape.1 to_equal "set-mode:normal"
val insert_commandline = svim_shell_classify_line(SvimMode.Insert, ":w")
expect insert_commandline.0 to_equal "dispatch"
expect insert_commandline.1 to_equal ":w"
```

</details>

#### renders session status and buffer listings

1. var session = SvimSession new
2. session open text
3. expect tui contains
4. expect tui contains
5. expect buffers contains
6. expect buffers contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.open_text("/tmp/alpha.txt", "alpha")
val tui = svim_render_tui(session)
expect tui.contains("mode NORMAL") to_equal true
expect tui.contains("/tmp/alpha.txt") to_equal true
val buffers = svim_render_buffer_list(session)
expect buffers.contains("[No Name]") to_equal true
expect buffers.contains("/tmp/alpha.txt") to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svim/tui_shell_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svim host shell helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
