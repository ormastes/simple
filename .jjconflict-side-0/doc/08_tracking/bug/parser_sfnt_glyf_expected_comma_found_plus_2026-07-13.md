# Bug: `EXPR as TYPE < ...` misparsed as generic-args list ("expected Comma, found Plus")

**ID:** parser_sfnt_glyf_expected_comma_found_plus_2026-07-13
**Filed:** 2026-07-13
**Status:** SOURCE FIXED in Rust and pure-Simple parser owners (2026-07-15);
focused test execution pending
**Severity:** P2 — load-path-only parse failure blocking a showcase app
**Component:** compiler frontend / parser (both deployed self-hosted `bin/simple`
and the fresh seed reject the same input)

## Symptom

`bin/simple run examples/06_io/ui/graphics_2d_showcase.spl` failed with:
```
error: compile failed: parse: in ".../src/lib/common/encoding/sfnt_glyf.spl": Unexpected token: expected Comma, found Plus
```
`bin/simple check src/lib/common/encoding/sfnt_glyf.spl` does NOT reproduce
(parses fine standalone) — the failure only appears via the module-load path
(`use std.common.encoding.sfnt_glyf.*` from another module).

## Root cause (bisected)

`X as TYPE < (Y + 1) * Z` — after `as TYPE`, the parser speculatively
continues into what it thinks is a generic-argument list (`TYPE<...>`) rather
than closing the cast and treating `<` as less-than. When the "argument" is an
arithmetic expression, it hits `+` where it expects a comma. Minimal isolated
repro (fails to parse):
```simple
if x as i64 < y: ...
if loca_length as i64 < loca_min_bytes: ...   # "expected Comma, found Colon"
if x < (a + 1) * b: ...                        # "expected Comma, found Plus"
```
Wrapping the cast in parens (`(X as TYPE) < ...`) fixes it in all variants —
confirmed by isolated repro at
`/private/tmp/.../scratchpad/verify/iso7.spl`. Sibling defect: same family as
`vulkan_font_discovery_expected_comma_plus_2026-07-13.md` (there the ambiguous
operator is `|` for union types instead of `<` for generics).

## Fix applied

`src/lib/common/encoding/sfnt_glyf.spl`, `parse_sfnt_glyf_outline` /
`_hmtx`: parenthesized the cast and hoisted the RHS arithmetic into a `val`:
```
-    if loca_table.length as i64 < (num_glyphs + 1) * entry_size:
+    val loca_min_bytes = (num_glyphs + 1) * entry_size
+    if (loca_table.length as i64) < loca_min_bytes:
```
```
-    if glyph_id as i64 < long_metrics:
+    if (glyph_id as i64) < long_metrics:
```

## Parser fix (2026-07-15)

Both parser owners now use a scoped cast-type entrypoint. In cast context,
`TYPE<...>` remains a generic type only when `<` is adjacent to the type name;
a spaced `<` closes the cast and is left for expression parsing. Normal type
and declaration parsing still accepts spaced generic syntax, so this does not
globally tighten the language grammar.

- Rust: `parse_cast_type()` delegates to the shared single-type parser with
  spaced generics disabled; ordinary `parse_single_type()` keeps them enabled.
- Pure Simple: `parser_parse_cast_type()` delegates to
  `parser_parse_type_impl(false)`. A plain `TOK_LT` remains generic in cast
  types only when its source offset is adjacent to the type name; normal type
  parsing continues to accept spacing.
- Only the two `as` expression sites use the new Simple entrypoint; the `is`
  path and recursive inner-type parsing remain unchanged.

## Verification

Harness `use std.common.encoding.sfnt_glyf.*` now loads with no parse error.
Showcase (`examples/06_io/ui/graphics_2d_showcase.spl`) proceeds past this
file and the sibling `backend_vulkan_font.spl` parse error; it currently stops
on an unrelated 10s example-runner timeout (non-parse), reported separately.

Focused Rust regressions cover the less-than AST shape, adjacent generic casts,
and spaced generic declarations. The canonical pure-Simple parser spec covers
the less-than/cast AST shape and adjacent generic casts. These tests were added
with the source fix; execution is pending the parent bootstrap/build lane.
