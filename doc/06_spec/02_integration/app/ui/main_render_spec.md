# UI Main Render CLI Parsing Specification

> Tests the CLI argument parsing for the `simple ui render` command. The parse_render_args function converts raw CLI arguments into a RenderConfig, handling flags like --format, --adapter, --mode, --output, --theme, --demo, and positional file paths.

<!-- sdn-diagram:id=main_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=main_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

main_render_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=main_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Main Render CLI Parsing Specification

Tests the CLI argument parsing for the `simple ui render` command. The parse_render_args function converts raw CLI arguments into a RenderConfig, handling flags like --format, --adapter, --mode, --output, --theme, --demo, and positional file paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UI-RENDER-003 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/ui_render_feature_caret.md |
| Research | N/A |
| Source | `test/02_integration/app/ui/main_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the CLI argument parsing for the `simple ui render` command.
The parse_render_args function converts raw CLI arguments into a
RenderConfig, handling flags like --format, --adapter, --mode, --output,
--theme, --demo, and positional file paths.

## Key Concepts

| Concept | Description |
|---------|-------------|
| parse_render_args | Parses CLI args after "render" into RenderConfig |
| run_render | Dispatches render to appropriate adapter based on config |
| --format | Sets output format: text, html, both |
| --adapter | Selects app adapter: dashboard, llm_dashboard, word, etc. |
| --demo | Enables built-in demo asset with default path |

## Behavior

- parse_render_args skips the first arg ("render") and processes remaining flags
- --format sets config.format to the next arg value
- --adapter sets config.adapter_name to the next arg value
- --mode sets config.mode to the next arg value
- --output sets config.output_path to the target file
- --demo sets use_default_demo=true and asset_path to widget_matrix demo
- Bare positional args (not starting with --) set asset_path
- Unknown flags are silently skipped

## Scenarios

### parse_render_args Format Parsing

#### when --format is specified

#### sets format to html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--format", "html"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
```

</details>

#### sets format to both

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--format", "both"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("both")
```

</details>

#### sets format to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--format", "text"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("text")
```

</details>

#### when --format= is used

#### sets format with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--format=html"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
```

</details>

#### when no format is specified

#### defaults to text format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("text")
```

</details>

### parse_render_args Adapter Parsing

#### when --adapter is specified

#### sets adapter_name to dashboard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--adapter", "dashboard"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("dashboard")
```

</details>

#### sets adapter_name to word

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--adapter", "word"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("word")
```

</details>

#### sets adapter_name to llm_dashboard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--adapter", "llm_dashboard"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("llm_dashboard")
```

</details>

#### when --adapter= is used

#### sets adapter with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--adapter=sheets"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("sheets")
```

</details>

#### when no adapter is specified

#### defaults to empty adapter_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("")
```

</details>

### parse_render_args Demo Flag

#### when --demo is specified

#### sets use_default_demo to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--demo"]
val cfg = parse_render_args(args)
expect(cfg.use_default_demo).to_equal(true)
```

</details>

<details>
<summary>Advanced: sets asset_path to widget_matrix demo</summary>

#### sets asset_path to widget_matrix demo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--demo"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_contain("widget_matrix")
```

</details>


</details>

#### sets asset_path ending with .ui.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--demo"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_end_with(".ui.sdn")
```

</details>

### parse_render_args File Path

#### when a file path is given

#### sets asset_path from positional arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "file.ui.sdn"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_equal("file.ui.sdn")
```

</details>

#### sets asset_path for nested path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "examples/06_io/ui/test.ui.sdn"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_equal("examples/06_io/ui/test.ui.sdn")
```

</details>

### parse_render_args Combined Arguments

#### when multiple flags are combined

#### parses format and adapter together

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--format", "html", "--adapter", "dashboard"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
expect(cfg.adapter_name).to_equal("dashboard")
```

</details>

#### parses mode flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--mode", "spipe"]
val cfg = parse_render_args(args)
expect(cfg.mode).to_equal("spipe")
```

</details>

#### parses theme flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--theme", "light"]
val cfg = parse_render_args(args)
expect(cfg.theme).to_equal("light")
```

</details>

#### parses output flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--output", "out/render.html"]
val cfg = parse_render_args(args)
expect(cfg.output_path).to_equal("out/render.html")
```

</details>

#### parses short output flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "-o", "out/render.txt"]
val cfg = parse_render_args(args)
expect(cfg.output_path).to_equal("out/render.txt")
```

</details>

#### parses format adapter and file together

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--format", "html", "--adapter", "word", "myfile.ui.sdn"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
expect(cfg.adapter_name).to_equal("word")
expect(cfg.asset_path).to_equal("myfile.ui.sdn")
```

</details>

#### parses output with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["render", "--output=out/render.html"]
val cfg = parse_render_args(args)
expect(cfg.output_path).to_equal("out/render.html")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/ui_render_feature_caret.md](doc/05_design/ui_render_feature_caret.md)


</details>
