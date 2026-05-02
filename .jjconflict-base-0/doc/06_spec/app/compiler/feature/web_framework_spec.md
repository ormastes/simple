# Web Framework Specification

**Feature ID:** #WEB-001 to #WEB-011 | **Category:** Tools | Web Framework | **Status:** Planned

_Source: `test/feature/usage/web_framework_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### Basic Web Build

- ✅ builds simple .sui file
- ✅ generates HTML output
- ✅ generates manifest file
### Client Code Compilation

- ✅ compiles client code to WASM
- ✅ generates hydration script
- ✅ includes WASM loader in HTML
### Web Build Optimization

- ✅ minifies HTML when enabled
- ✅ optimizes WASM when enabled
### Event Bindings

- ✅ binds multiple events
- ✅ manifest contains binding info
### Web Project Initialization

- ✅ creates project directory
- ✅ creates app.sui template
### Web Build Error Handling

- ✅ fails for missing file
- ✅ fails for invalid syntax
### Output Configuration

- ✅ creates nested output directories
- ✅ uses custom module name

