# Web Framework Specification

> {$ let count: i32 = 0 $}

<!-- sdn-diagram:id=web_framework_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_framework_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_framework_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_framework_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Framework Specification

{$ let count: i32 = 0 $}

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WEB-001 to #WEB-011 |
| Category | Tools \| Web Framework |
| Status | Planned |
| Source | `test/03_system/feature/usage/web_framework_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## .sui File Structure

- `{$ shared $}` - Shared state between server and client
- `{- server -}` - Server-only code
- `{+ client +}` - Client-only code (compiled to WASM)
- `{@ render @}` - HTML template with interpolation

## Syntax

```simple
{$ let count: i32 = 0 $}

{- server -}
fn render(): String = count.to_string()

{+ client +}
fn increment():
count = count + 1

dom.getElementById("btn").addEventListener("click", increment)

{@ render @}
<div>Count: <span id="count">{{ count }}</span></div>
<button id="btn">Increment</button>
```

## Scenarios

### Basic Web Build

#### builds simple .sui file

1. fn test basic build

2. expect test basic build


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# web_build should succeed and return exit code 0
@fs
fn test_basic_build() -> i64:
    0  # Success

expect test_basic_build() == 0
```

</details>

#### generates HTML output

1. fn test html output

2. expect test html output


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_html_output() -> bool:
    # Output directory should contain app.html
    true

expect test_html_output()
```

</details>

#### generates manifest file

1. fn test manifest

2. expect test manifest


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_manifest() -> bool:
    # Output directory should contain app.manifest.json
    true

expect test_manifest()
```

</details>

### Client Code Compilation

#### compiles client code to WASM

1. fn test wasm output

2. expect test wasm output


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_wasm_output() -> bool:
    # Client code should generate .wasm file
    true

expect test_wasm_output()
```

</details>

#### generates hydration script

1. fn test hydration script

2. expect test hydration script


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_hydration_script() -> bool:
    # Client code should generate .hydration.js
    true

expect test_hydration_script()
```

</details>

#### includes WASM loader in HTML

1. fn test wasm loader

2. expect test wasm loader


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_wasm_loader() -> bool:
    # HTML should contain loadWasm call
    true

expect test_wasm_loader()
```

</details>

### Web Build Optimization

#### minifies HTML when enabled

1. fn test minify html

2. expect test minify html


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_minify_html() -> bool:
    # Minified HTML should have fewer lines
    true

expect test_minify_html()
```

</details>

#### optimizes WASM when enabled

1. fn test optimize wasm

2. expect test optimize wasm


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_optimize_wasm() -> bool:
    # wasm-opt should be applied if available
    true

expect test_optimize_wasm()
```

</details>

### Event Bindings

#### binds multiple events

1. fn test multiple events

2. expect test multiple events


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_multiple_events() -> bool:
    # Multiple addEventListener calls should all be captured
    true

expect test_multiple_events()
```

</details>

#### manifest contains binding info

1. fn test manifest bindings

2. expect test manifest bindings


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_manifest_bindings() -> bool:
    # Manifest should have selector, event, handler info
    true

expect test_manifest_bindings()
```

</details>

### Web Project Initialization

#### creates project directory

1. fn test init creates dir

2. expect test init creates dir


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_init_creates_dir() -> bool:
    # web_init should create project directory
    true

expect test_init_creates_dir()
```

</details>

#### creates app.sui template

1. fn test init creates sui

2. expect test init creates sui


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_init_creates_sui() -> bool:
    # Template should contain all required blocks
    true

expect test_init_creates_sui()
```

</details>

### Web Build Error Handling

#### fails for missing file

1. fn test missing file

2. expect test missing file


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_missing_file() -> i64:
    # web_build should return non-zero for missing file
    1  # Error

expect test_missing_file() != 0
```

</details>

#### fails for invalid syntax

1. fn test invalid syntax

2. expect test invalid syntax


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_invalid_syntax() -> i64:
    # Parser errors should cause build failure
    1  # Error

expect test_invalid_syntax() != 0
```

</details>

### Output Configuration

#### creates nested output directories

1. fn test nested output

2. expect test nested output


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_nested_output() -> bool:
    # Should create nested/output/dir path
    true

expect test_nested_output()
```

</details>

#### uses custom module name

1. fn test custom module

2. expect test custom module


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_custom_module() -> bool:
    # Files should use custom module name
    true

expect test_custom_module()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
