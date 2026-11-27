# Native MIR rejects a text tuple literal as an optional tuple fallback

**Status** Fixed in native MIR lowering. Observed with the native Phase 3 compiler building the Phase 4 MCP server on Darwin arm64.

A function returning `(text, text)?` and a fallback literal containing two strings have matching element types. The native compiler reports `null coalesce fallback does not match declared tuple owner` for the expression below.

```simple
fn range_or_default(lines: [text], unit_name: text) -> text:
    val bounds = _bf_unit_range(lines, unit_name) ?? ("0", "0")
    return bounds.0 + "," + bounds.1
```

Here `_bf_unit_range` is the function in `src/compiler/90.tools/fix/rules/impl_/bound_late_cast_fix.spl`. A one-module native build containing that function, its literal parser and the coalescing expression reproduced the product failure. An explicit presence test compiled and returned the declared numeric endpoints. The constrained adapter now skips unrecognized ranges because it requires actual declared bounds.

When the lowered fallback has no recorded tuple type, `optional_tuple_fallback_matches` checks each literal element against its declared slot. It uses the existing source-type witness and requires an exact arity and type match.

The native fixtures under `test/fixtures/native_optional_tuple_literal_coalesce/` cover both optional branches, a third field, and a boolean in a text slot. The valid program exits zero. Both invalid programs must fail MIR lowering with `null coalesce fallback does not match declared tuple owner`.
