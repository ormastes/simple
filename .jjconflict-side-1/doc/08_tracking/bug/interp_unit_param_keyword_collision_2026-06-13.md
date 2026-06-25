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
- **Workaround LANDED** (pure `.spl`): bench code renames `unit` → `unit_label`
  (`src/app/test/bench/bench_harness.spl`, `bench_report.spl`). Keystone unblocked — struct-based
  `bench_run_warm`/`bench_emit` and db/web/os doc emission can now proceed.
- **General seed fix: OPEN** — pending user authorization (affects all user code with `unit`).
- Treat `unit` as effectively reserved until the seed fix lands.
