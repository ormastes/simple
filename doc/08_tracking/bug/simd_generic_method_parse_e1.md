# Bug: simd_generic_method_parse_e1 — Generic<X>.method() and Generic<X>::method() fail to parse

**Filed:** 2026-05-02
**Filed by:** E1 (Wave-E parser agent)
**Status:** OUT OF SCOPE for .spl edits — requires Rust seed parser fix or full bootstrap rebuild

---

## Symptom

Both of these expression forms fail at parse time:

```
Foo<Int>.bar()      # error: parse error: Unexpected token: expected expression, found Dot
Foo<Int>::bar()     # error: parse error: Unexpected token: expected expression, found DoubleColon
```

Reproduced with minimal probes:
```
fn main():
    val x = Foo<Int>.bar()   # → "expected expression, found Dot"
    val x = Foo<Int>::bar()  # → "expected expression, found DoubleColon"
```

Note: `Foo.bar()` and `Foo::bar()` (no generics) both work fine.

---

## Root Cause

The Rust seed parser (at `src/compiler_rust/target/bootstrap/simple`) handles expression parsing
independently of the self-hosted Simple parser in `src/compiler/10.frontend/core/parser_primary.spl`
and `parser_expr.spl`.

When parsing `Foo<Int>.bar()`, the seed parser:
1. Parses `Foo` as an identifier
2. Sees `<` as TOK_LT (comparison operator) — NOT TOK_LT_GENERIC
3. Parses `Foo < Int` as a less-than comparison expression
4. Then sees `> .bar()` — tries to parse `.bar()` as the RHS of `>`
5. Fails: `.` is not a valid start of a primary expression → "expected expression, found Dot"

The same logic applies to `Foo<Int>::bar()` — `::` is not a valid primary expression start.

**Confirmed:** Editing `parser_primary.spl` or `parser_expr.spl` has NO effect on `bin/simple` output
because `bin/simple` invokes the pre-compiled Rust seed binary. A `parser_warn("ZZZ-IDENT-PROBE")`
added to `parser_primary.spl:396` did not appear in `bin/simple` output.

**Token note:** `TOK_LT_GENERIC = 86` is only emitted by the lexer in declaration/type contexts
(e.g., `class Box<T>`). In expression context, `<` is always `TOK_LT`. There is no lookahead
disambiguation in expression position.

---

## Impact on SIMD Tests

The `Mask<Vec4f>::all_ones()` and `ScalableVec<f32>::splat(1.0)` call forms are blocked.
Current workarounds used in SIMD specs:
- `Mask<Vec4f>::all_ones_n(4)` — uses deprecated `::` form (works because no `<X>` before `::`)
- Constructor form `Mask(...)` — avoids the issue

Tests in `test/unit/lib/simd/mask_spec.spl` and `scalable_spec.spl` currently PASS using
workaround forms without generics before `::`.

---

## Fix Required

The fix must be made in the Rust seed parser source:

1. Find the expression parser in `src/compiler_rust/compiler/src/` (the bootstrap binary's
   parser handles `Ident` then stops before `<`). Add lookahead: when `IDENT` is followed by `<`,
   attempt to parse a generic type argument list `<TypeArgs>`. If parsing succeeds and next token
   is `.` or `::`, treat the whole `IDENT<TypeArgs>` as a typed expression base and continue
   with postfix parsing.

2. After the Rust fix, run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` to rebuild the
   seed binary.

3. The Simple-side parser files (`parser_primary.spl`, `parser_expr.spl`) will also need a
   matching fix so they stay in sync with the seed for future bootstrap stages.

---

## Workarounds

Until the seed is fixed:
- Use `TypeName.static_method()` form (no generic params in expression) — works fine
- Use `TypeName::static_method()` form — works (deprecated warning, but functional)
- Avoid `Generic<X>.method()` and `Generic<X>::method()` in all source code

---

## Related

- Task: E1 (Wave-E, parser fix assignment)
- `src/compiler/10.frontend/core/parser_primary.spl` — Simple-side IDENT handler (line 396)
- `src/compiler/10.frontend/core/parser_expr.spl` — Simple-side postfix loop (line 646)
- `src/compiler/10.frontend/core/tokens.spl` — TOK_LT_GENERIC = 86, TOK_COLON_COLON = 162
- `test/unit/lib/simd/mask_spec.spl` — uses workaround :: form
- `test/unit/lib/simd/scalable_spec.spl` — uses workaround constructor form
