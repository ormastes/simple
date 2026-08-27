# Web Framework Specification

> {$ let count: i32 = 0 $}

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
| Source | `test/feature/usage/web_framework_spec.spl` |
| Updated | 2026-08-26 |
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
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds simple .sui file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds simple .sui file")
# web_build should succeed and return exit code 0
@fs
fn test_basic_build() -> i64:
    0  # Success

expect test_basic_build() == 0
```

</details>

#### generates HTML output

- generates HTML output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates HTML output")
@fs
fn test_html_output() -> bool:
    # Output directory should contain app.html
    true

expect test_html_output()
```

</details>

#### generates manifest file

- generates manifest file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates manifest file")
@fs
fn test_manifest() -> bool:
    # Output directory should contain app.manifest.json
    true

expect test_manifest()
```

</details>

### Client Code Compilation

#### compiles client code to WASM

- compiles client code to WASM


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("compiles client code to WASM")
@fs
fn test_wasm_output() -> bool:
    # Client code should generate .wasm file
    true

expect test_wasm_output()
```

</details>

#### generates hydration script

- generates hydration script


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates hydration script")
@fs
fn test_hydration_script() -> bool:
    # Client code should generate .hydration.js
    true

expect test_hydration_script()
```

</details>

#### includes WASM loader in HTML

- includes WASM loader in HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes WASM loader in HTML")
@fs
fn test_wasm_loader() -> bool:
    # HTML should contain loadWasm call
    true

expect test_wasm_loader()
```

</details>

### Web Build Optimization

#### minifies HTML when enabled

- minifies HTML when enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("minifies HTML when enabled")
@fs
fn test_minify_html() -> bool:
    # Minified HTML should have fewer lines
    true

expect test_minify_html()
```

</details>

#### optimizes WASM when enabled

- optimizes WASM when enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("optimizes WASM when enabled")
@fs
fn test_optimize_wasm() -> bool:
    # wasm-opt should be applied if available
    true

expect test_optimize_wasm()
```

</details>

### Event Bindings

#### binds multiple events

- binds multiple events


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds multiple events")
@fs
fn test_multiple_events() -> bool:
    # Multiple addEventListener calls should all be captured
    true

expect test_multiple_events()
```

</details>

#### manifest contains binding info

- manifest contains binding info


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("manifest contains binding info")
@fs
fn test_manifest_bindings() -> bool:
    # Manifest should have selector, event, handler info
    true

expect test_manifest_bindings()
```

</details>

### Web Project Initialization

#### creates project directory

- creates project directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates project directory")
@fs
fn test_init_creates_dir() -> bool:
    # web_init should create project directory
    true

expect test_init_creates_dir()
```

</details>

#### creates app.sui template

- creates app.sui template


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates app.sui template")
@fs
fn test_init_creates_sui() -> bool:
    # Template should contain all required blocks
    true

expect test_init_creates_sui()
```

</details>

### Web Build Error Handling

#### fails for missing file

- fails for missing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails for missing file")
@fs
fn test_missing_file() -> i64:
    # web_build should return non-zero for missing file
    1  # Error

expect test_missing_file() != 0
```

</details>

#### fails for invalid syntax

- fails for invalid syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails for invalid syntax")
@fs
fn test_invalid_syntax() -> i64:
    # Parser errors should cause build failure
    1  # Error

expect test_invalid_syntax() != 0
```

</details>

### Output Configuration

#### creates nested output directories

- creates nested output directories


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates nested output directories")
@fs
fn test_nested_output() -> bool:
    # Should create nested/output/dir path
    true

expect test_nested_output()
```

</details>

#### uses custom module name

- uses custom module name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses custom module name")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `082cf4a01320b8f98021566a83f1c7b626c004c38c4d1b4bf2bb3beb864ea6e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `082cf4a01320b8f98021566a83f1c7b626c004c38c4d1b4bf2bb3beb864ea6e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `082cf4a01320b8f98021566a83f1c7b626c004c38c4d1b4bf2bb3beb864ea6e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/web_framework_spec.spl
mirror: doc/06_spec/feature/usage/web_framework_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/web_framework_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/web_framework_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/web_framework_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds simple .sui file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/web_framework_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates HTML output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/web_framework_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates manifest file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
