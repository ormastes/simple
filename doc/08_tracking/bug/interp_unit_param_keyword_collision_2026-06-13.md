# BUG: parameter/variable named `unit` collides with the `Unit` keyword token (seed parser)

- **ID:** `interp_unit_param_keyword_collision`
- **Severity:** P1 (any user code with a `unit` parameter/variable mis-parses or fails lookup)
- **Found:** 2026-06-13, perf-umbrella (diagnosing the bench `make_bench_result` failure)
- **Supersedes:** `interp_cross_module_struct_return_unit_2026-06-13.md` (that framing was WRONG —
  it was never a cross-module struct ABI bug; see "Misattribution" below).

## Root cause (verified)
The seed parser handles the `unit` token inconsistently:
- **Expression context** — `src/compiler_rust/parser/src/expressions/primary/identifiers.rs:74`
  `TokenKind::Unit => self.parse_keyword_identifier("Unit")` → produces `Identifier("Unit")` (capital).
- **Declaration context** — `expect_identifier()` in `parser_helpers.rs` returns `"unit"` (lowercase).

So a parameter/variable declared `unit` is stored as `"unit"` but, when referenced in a body
expression, is looked up as `"Unit"` → "Unknown variable: Unit" in the HIR lowerer and the
interpreter fallback. A bare `unit` as a full expression instead parses as the Unit keyword
("expected identifier, found Newline").

## Repro (single file — no cross-module needed)
```simple
fn f(unit: text) -> text:
    unit            # parsed as keyword Unit -> fails
fn main():
    print(f("ms"))
```
Fixture: `test/fixtures/cross_module_struct/mod_unit_param.spl`. Renaming `unit` → `unit_label`
makes it pass (`/tmp/unit_rename_test.spl` printed `ms`).

## Misattribution corrected
The original report blamed cross-module struct return because the failing case
(`make_bench_result`) had a `unit: text` parameter while the working same-module case did not.
After renaming the `unit` parameter, `make_bench_result` returns a struct across modules
correctly: a proof program printed `value=42` / `unit=ops`. **There is no cross-module struct bug.**

## Ownership verdict
Fix site is the **Rust seed** parser (`identifiers.rs:74`). The self-hosted compiler has no
pure-`.spl` parser crate (`src/compiler/10.parser/` is empty; it consumes the seed AST). So the
**real fix requires a seed change** (`"Unit"` → `"unit"`), which per CLAUDE.md needs explicit
authorization + `cargo build` + `bootstrap-from-scratch.sh --deploy` + smoke-test. Same file/pattern
as the prior `Slice`/`Flat` fix (2026-06-12, comment ~line 78).

## Status
- **RESOLVED 2026-06-18** — general seed fix landed + rebuilt + deployed + verified. Two parts:
  1. Expression context (`expressions/primary/identifiers.rs`): `TokenKind::Unit =>
     parse_keyword_identifier("unit")` (lowercase) — committed earlier; became live once the seed
     was rebuilt this session.
  2. Statement context (`parser_impl/core.rs`, the `TokenKind::Unit` arm): added `peek_next()`
     lookahead — `unit <Identifier>:` parses as a unit-type declaration; a bare `unit` (anything
     else after it) parses as an expression/identifier. Mirrors the Comptime/From disambiguation.
  Verified live on the deployed seed (`x86_64-unknown-linux-gnu`):
  `fn f(unit: text): unit` (bare implicit return), `return unit`, and `val r = unit` all print `ms`;
  `unit Duration: i64 as ms` declarations still parse (regression OK).
- The earlier pure-`.spl` workaround (rename `unit` → `unit_label` in bench code) is no longer
  required, but is harmless and left in place.
- `unit` is no longer effectively reserved — it works as a parameter/variable name.
