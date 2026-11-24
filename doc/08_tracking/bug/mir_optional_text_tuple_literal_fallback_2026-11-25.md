# Native MIR rejects a text tuple literal as an optional tuple fallback

**Status** Open for general lowering. Observed with the native Phase 3 compiler building the Phase 4 MCP server on Darwin arm64.

A function returning `(text, text)?` and a fallback literal containing two strings have matching element types. The native compiler reports `null coalesce fallback does not match declared tuple owner` for the expression below.

```simple
fn range_or_default(lines: [text], unit_name: text) -> text:
    val bounds = _bf_unit_range(lines, unit_name) ?? ("0", "0")
    return bounds.0 + "," + bounds.1
```

Here `_bf_unit_range` is the function in `src/compiler/90.tools/fix/rules/impl_/bound_late_cast_fix.spl`. A one-module native build containing that function, its literal parser and the coalescing expression reproduced the product failure. An explicit presence test compiled and returned the declared numeric endpoints. The constrained adapter now skips unrecognized ranges because it requires actual declared bounds.

In `_MirLoweringExpr/result_tuple_payload.spl`, `optional_tuple_fallback_matches` asks `receiver_declared_or_result_type` for an owner. That path uses a declared variable or remembered result type. A fix for the general language case must establish the literal's tuple element types and continue rejecting mismatched arity and element types.
