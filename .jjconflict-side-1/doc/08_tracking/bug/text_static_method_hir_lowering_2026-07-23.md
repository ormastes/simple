# HIR: static method call on builtin type name `text` unresolved (entry-closure)

**Found:** 2026-07-23, MCP native rebuild campaign (rMCP11).
**Status:** OPEN — call site worked around (std.string_core.char_from_code).

## Symptom
`text.from_char_code(ch)` in app.mcp.main_lazy_query_tools dies during
native entry-closure HIR lowering with `unresolved name: text`: the receiver
`text` is lowered as a value identifier (Var/NamedVar) instead of being
recognized as the builtin type and dispatched as `HirExprKind.StaticCall`.
The interpreter path accepts the same form.

## Expected
`<builtin type name>.<method>(args)` (text/i64/f64/...) should lower to
StaticCall on the corresponding type, matching interpreter semantics —
or the form should be rejected uniformly in both paths.

## Repro sketch
```simple
fn f(ch: i64) -> text:
    text.from_char_code(ch)
```
native-build --entry-closure over a module calling `f` → unresolved name: text.

## Workaround applied
`use std.string_core.{char_from_code}` and call the free function
(src/app/mcp/main_lazy_query_tools.spl `_mcp_json_escape`).
