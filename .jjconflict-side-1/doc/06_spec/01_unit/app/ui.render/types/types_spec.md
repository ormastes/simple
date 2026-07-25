# UI Render Contract Types Specification

> Tests the shared render contract types used by all app adapters (dashboard, llm_dashboard, office). Validates factory methods, default values, and result construction for RenderConfig, RenderRequest, and RenderResult.

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
types_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Render Contract Types Specification

Tests the shared render contract types used by all app adapters (dashboard, llm_dashboard, office). Validates factory methods, default values, and result construction for RenderConfig, RenderRequest, and RenderResult.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UI-RENDER-001 |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/ui_render_feature_caret.md |
| Research | N/A |
| Source | `test/01_unit/app/ui.render/types/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the shared render contract types used by all app adapters
(dashboard, llm_dashboard, office). Validates factory methods,
default values, and result construction for RenderConfig,
RenderRequest, and RenderResult.

## Key Concepts

| Concept | Description |
|---------|-------------|
| RenderConfig | Configuration for a render request (mode, backend, format, dimensions) |
| RenderResult | Result of a render operation (text_output, html_output, metadata) |
| RenderRequest | Combines config with export targets |
| Factory methods | Static constructors: default(), text_export(), html_export(), empty(), text(), html(), both() |

## Behavior

- RenderConfig.default() returns sensible defaults (80x24, "text" format, "dark" theme)
- RenderConfig.text_export() and html_export() set the format field
- RenderResult.empty() returns empty strings for all output fields
- RenderResult.text(content) sets text_output only
- RenderResult.html(content) sets html_output only
- RenderResult.both(t, h) sets both output fields and format to "both"

## Scenarios

### RenderConfig Factory Methods

#### default()

#### returns mode as render

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.mode).to_equal("render")
```

</details>

#### returns backend as auto

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.backend).to_equal("auto")
```

</details>

#### returns format as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.format).to_equal("text")
```

</details>

#### returns width of 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.width).to_equal(80)
```

</details>

#### returns height of 24

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.height).to_equal(24)
```

</details>

#### returns theme as dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.theme).to_equal("dark")
```

</details>

#### returns empty asset_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.asset_path).to_equal("")
```

</details>

#### returns empty output_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.output_path).to_equal("")
```

</details>

#### returns empty adapter_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.adapter_name).to_equal("")
```

</details>

#### returns use_default_demo as false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
expect(cfg.use_default_demo).to_equal(false)
```

</details>

#### text_export()

#### sets format to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.text_export()
expect(cfg.format).to_equal("text")
```

</details>

#### inherits default width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.text_export()
expect(cfg.width).to_equal(80)
```

</details>

#### inherits default height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.text_export()
expect(cfg.height).to_equal(24)
```

</details>

#### html_export()

#### sets format to html

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.html_export()
expect(cfg.format).to_equal("html")
```

</details>

#### inherits default theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.html_export()
expect(cfg.theme).to_equal("dark")
```

</details>

#### inherits default backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.html_export()
expect(cfg.backend).to_equal("auto")
```

</details>

### RenderResult Factory Methods

#### empty()

#### returns format as text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.empty()
expect(result.format).to_equal("text")
```

</details>

#### returns empty text_output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.empty()
expect(result.text_output).to_equal("")
```

</details>

#### returns empty html_output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.empty()
expect(result.html_output).to_equal("")
```

</details>

#### text(content)

#### sets text_output to provided content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.text("hello world")
expect(result.text_output).to_equal("hello world")
```

</details>

#### sets format to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.text("hello")
expect(result.format).to_equal("text")
```

</details>

#### leaves html_output empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.text("hello")
expect(result.html_output).to_equal("")
```

</details>

#### html(content)

#### sets html_output to provided content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.html("<h1>hello</h1>")
expect(result.html_output).to_equal("<h1>hello</h1>")
```

</details>

#### sets format to html

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.html("<p>test</p>")
expect(result.format).to_equal("html")
```

</details>

#### leaves text_output empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.html("<p>test</p>")
expect(result.text_output).to_equal("")
```

</details>

#### both(text_content, html_content)

#### sets text_output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.both("plain", "<b>rich</b>")
expect(result.text_output).to_equal("plain")
```

</details>

#### sets html_output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.both("plain", "<b>rich</b>")
expect(result.html_output).to_equal("<b>rich</b>")
```

</details>

#### sets format to both

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = RenderResult.both("plain", "<b>rich</b>")
expect(result.format).to_equal("both")
```

</details>

### RenderRequest Construction

#### from_config

#### preserves config format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.html_export()
val req = RenderRequest.from_config(cfg)
expect(req.config.format).to_equal("html")
```

</details>

#### preserves config mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RenderConfig.default()
val req = RenderRequest.from_config(cfg)
expect(req.config.mode).to_equal("render")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/ui_render_feature_caret.md](doc/05_design/ui_render_feature_caret.md)


</details>
