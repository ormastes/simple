# UI Main Render CLI Parsing Specification

> Tests the CLI argument parsing for the `simple ui render` command. The parse_render_args function converts raw CLI arguments into a RenderConfig, handling flags like --format, --adapter, --mode, --output, --theme, --demo, and positional file paths.

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
| Source | `test/integration/app/ui/main_render_spec.spl` |
| Updated | 2026-08-26 |
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

- sets format to html
   - Expected: cfg.format equals `html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets format to html")
val args = ["render", "--format", "html"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
```

</details>

#### sets format to both

- sets format to both
   - Expected: cfg.format equals `both`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets format to both")
val args = ["render", "--format", "both"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("both")
```

</details>

#### sets format to text

- sets format to text
   - Expected: cfg.format equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets format to text")
val args = ["render", "--format", "text"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("text")
```

</details>

#### when --format= is used

#### sets format with equals syntax

- sets format with equals syntax
   - Expected: cfg.format equals `html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets format with equals syntax")
val args = ["render", "--format=html"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
```

</details>

#### when no format is specified

#### defaults to text format

- defaults to text format
   - Expected: cfg.format equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defaults to text format")
val args = ["render"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("text")
```

</details>

### parse_render_args Adapter Parsing

#### when --adapter is specified

#### sets adapter_name to dashboard

- sets adapter_name to dashboard
   - Expected: cfg.adapter_name equals `dashboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets adapter_name to dashboard")
val args = ["render", "--adapter", "dashboard"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("dashboard")
```

</details>

#### sets adapter_name to word

- sets adapter_name to word
   - Expected: cfg.adapter_name equals `word`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets adapter_name to word")
val args = ["render", "--adapter", "word"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("word")
```

</details>

#### sets adapter_name to llm_dashboard

- sets adapter_name to llm_dashboard
   - Expected: cfg.adapter_name equals `llm_dashboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets adapter_name to llm_dashboard")
val args = ["render", "--adapter", "llm_dashboard"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("llm_dashboard")
```

</details>

#### when --adapter= is used

#### sets adapter with equals syntax

- sets adapter with equals syntax
   - Expected: cfg.adapter_name equals `sheets`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets adapter with equals syntax")
val args = ["render", "--adapter=sheets"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("sheets")
```

</details>

#### when no adapter is specified

#### defaults to empty adapter_name

- defaults to empty adapter_name
   - Expected: cfg.adapter_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defaults to empty adapter_name")
val args = ["render"]
val cfg = parse_render_args(args)
expect(cfg.adapter_name).to_equal("")
```

</details>

### parse_render_args Demo Flag

#### when --demo is specified

#### sets use_default_demo to true

- sets use_default_demo to true
   - Expected: cfg.use_default_demo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets use_default_demo to true")
val args = ["render", "--demo"]
val cfg = parse_render_args(args)
expect(cfg.use_default_demo).to_equal(true)
```

</details>

<details>
<summary>Advanced: sets asset_path to widget_matrix demo</summary>

#### sets asset_path to widget_matrix demo

- sets asset_path to widget_matrix demo


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets asset_path to widget_matrix demo")
val args = ["render", "--demo"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_contain("widget_matrix")
```

</details>


</details>

#### sets asset_path ending with .ui.sdn

- sets asset_path ending with .ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets asset_path ending with .ui.sdn")
val args = ["render", "--demo"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_end_with(".ui.sdn")
```

</details>

### parse_render_args File Path

#### when a file path is given

#### sets asset_path from positional arg

- sets asset_path from positional arg
   - Expected: cfg.asset_path equals `file.ui.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets asset_path from positional arg")
val args = ["render", "file.ui.sdn"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_equal("file.ui.sdn")
```

</details>

#### sets asset_path for nested path

- sets asset_path for nested path
   - Expected: cfg.asset_path equals `examples/ui/test.ui.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets asset_path for nested path")
val args = ["render", "examples/ui/test.ui.sdn"]
val cfg = parse_render_args(args)
expect(cfg.asset_path).to_equal("examples/ui/test.ui.sdn")
```

</details>

### parse_render_args Combined Arguments

#### when multiple flags are combined

#### parses format and adapter together

- parses format and adapter together
   - Expected: cfg.format equals `html`
   - Expected: cfg.adapter_name equals `dashboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses format and adapter together")
val args = ["render", "--format", "html", "--adapter", "dashboard"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
expect(cfg.adapter_name).to_equal("dashboard")
```

</details>

#### parses mode flag

- parses mode flag
   - Expected: cfg.mode equals `spipe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses mode flag")
val args = ["render", "--mode", "spipe"]
val cfg = parse_render_args(args)
expect(cfg.mode).to_equal("spipe")
```

</details>

#### parses theme flag

- parses theme flag
   - Expected: cfg.theme equals `light`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses theme flag")
val args = ["render", "--theme", "light"]
val cfg = parse_render_args(args)
expect(cfg.theme).to_equal("light")
```

</details>

#### parses output flag

- parses output flag
   - Expected: cfg.output_path equals `out/render.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses output flag")
val args = ["render", "--output", "out/render.html"]
val cfg = parse_render_args(args)
expect(cfg.output_path).to_equal("out/render.html")
```

</details>

#### parses short output flag

- parses short output flag
   - Expected: cfg.output_path equals `out/render.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses short output flag")
val args = ["render", "-o", "out/render.txt"]
val cfg = parse_render_args(args)
expect(cfg.output_path).to_equal("out/render.txt")
```

</details>

#### parses format adapter and file together

- parses format adapter and file together
   - Expected: cfg.format equals `html`
   - Expected: cfg.adapter_name equals `word`
   - Expected: cfg.asset_path equals `myfile.ui.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses format adapter and file together")
val args = ["render", "--format", "html", "--adapter", "word", "myfile.ui.sdn"]
val cfg = parse_render_args(args)
expect(cfg.format).to_equal("html")
expect(cfg.adapter_name).to_equal("word")
expect(cfg.asset_path).to_equal("myfile.ui.sdn")
```

</details>

#### parses output with equals syntax

- parses output with equals syntax
   - Expected: cfg.output_path equals `out/render.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses output with equals syntax")
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

- **Design:** `doc/05_design/ui_render_feature_caret.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b2a260e992238f894efb1b6a1dd3f3ac5f0dfd5fe9e7c4a1b066007b10f9ad18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b2a260e992238f894efb1b6a1dd3f3ac5f0dfd5fe9e7c4a1b066007b10f9ad18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b2a260e992238f894efb1b6a1dd3f3ac5f0dfd5fe9e7c4a1b066007b10f9ad18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/ui/main_render_spec.spl
mirror: doc/06_spec/integration/app/ui/main_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/ui/main_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/ui/main_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/ui/main_render_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets format to html' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/ui/main_render_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets format to both' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/ui/main_render_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets format to text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
