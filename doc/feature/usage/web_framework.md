# Web Framework Specification
*Source:* `test/feature/usage/web_framework_spec.spl`
**Feature IDs:** #WEB-001 to #WEB-011  |  **Category:** Tools | Web Framework  |  **Status:** Planned

## Overview



Tests the Simple web framework (.sui files) including:
- Web build command
- Server/client code splitting
- WASM compilation
- Hydration scripts
- HTML minification
- Web project initialization
- Error handling

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

## Feature: Basic Web Build

## HTML Generation

    Tests basic web build functionality.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | builds simple .sui file | pass |
| 2 | generates HTML output | pass |
| 3 | generates manifest file | pass |

**Example:** builds simple .sui file
    Then  expect test_basic_build() == 0

**Example:** generates HTML output
    Then  expect test_html_output()

**Example:** generates manifest file
    Then  expect test_manifest()

## Feature: Client Code Compilation

## WASM Generation

    Tests client code compilation to WebAssembly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | compiles client code to WASM | pass |
| 2 | generates hydration script | pass |
| 3 | includes WASM loader in HTML | pass |

**Example:** compiles client code to WASM
    Then  expect test_wasm_output()

**Example:** generates hydration script
    Then  expect test_hydration_script()

**Example:** includes WASM loader in HTML
    Then  expect test_wasm_loader()

## Feature: Web Build Optimization

## HTML and WASM Optimization

    Tests minification and optimization options.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | minifies HTML when enabled | pass |
| 2 | optimizes WASM when enabled | pass |

**Example:** minifies HTML when enabled
    Then  expect test_minify_html()

**Example:** optimizes WASM when enabled
    Then  expect test_optimize_wasm()

## Feature: Event Bindings

## DOM Event Registration

    Tests client-side event binding generation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | binds multiple events | pass |
| 2 | manifest contains binding info | pass |

**Example:** binds multiple events
    Then  expect test_multiple_events()

**Example:** manifest contains binding info
    Then  expect test_manifest_bindings()

## Feature: Web Project Initialization

## web init Command

    Tests project scaffolding.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates project directory | pass |
| 2 | creates app.sui template | pass |

**Example:** creates project directory
    Then  expect test_init_creates_dir()

**Example:** creates app.sui template
    Then  expect test_init_creates_sui()

## Feature: Web Build Error Handling

## Build Failure Cases

    Tests graceful error handling.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | fails for missing file | pass |
| 2 | fails for invalid syntax | pass |

**Example:** fails for missing file
    Then  expect test_missing_file() != 0

**Example:** fails for invalid syntax
    Then  expect test_invalid_syntax() != 0

## Feature: Output Configuration

## Build Output Options

    Tests output directory and module naming.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates nested output directories | pass |
| 2 | uses custom module name | pass |

**Example:** creates nested output directories
    Then  expect test_nested_output()

**Example:** uses custom module name
    Then  expect test_custom_module()


