# Web Framework Specification

Tests the Simple web framework (.sui files) including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WEB-001 to #WEB-011 |
| Category | Tools \| Web Framework |
| Status | Planned |
| Source | `test/feature/usage/web_framework_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/web_framework/result.json` |

## Scenarios

- builds simple .sui file
- generates HTML output
- generates manifest file
- compiles client code to WASM
- generates hydration script
- includes WASM loader in HTML
- minifies HTML when enabled
- optimizes WASM when enabled
- binds multiple events
- manifest contains binding info
- creates project directory
- creates app.sui template
- fails for missing file
- fails for invalid syntax
- creates nested output directories
- uses custom module name
