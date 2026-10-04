# Seed JIT: an `if` expression whose branch is `x as i64` evaluates to 3

- **Filed:** 2026-10-04
- **Area:** Rust seed JIT (Cranelift), HIR/MIR lowering of value-producing `if` with an `as` cast
- **Status:** FIXED 2026-10-04 (seed parser; see "Root cause" below)
- **Severity:** high — silent wrong numbers; breaks text layout in every JIT'd UI run

## Minimal repro

```simple
fn v1(g: i32) -> i64:
    val step: i64 = if g > 0: g as i64 else: 5
    step

fn v2(g: i32) -> i64:
    val step: i64 = if g > 0: g.to_i64() else: 5
    step

fn v3(g: i32) -> i64:
    val w = g as i64
    val step: i64 = if g > 0: w else: 5
    step

fn main():
    print "v1={v1(7200)} v2={v2(7200)} v3={v3(7200)}"
```

| engine | output |
|---|---|
| JIT (`SIMPLE_JIT_STRICT=1`, seed from origin/main 90c6e6ed27b) | `v1=3 v2=7200 v3=7200` |
| interpreter (`SIMPLE_EXECUTION_MODE=interpret`) | `v1=7200 v2=7200 v3=7200` |

Only the `as` cast **inside the if-expression branch** is wrong; `.to_i64()` in
the branch, or the cast hoisted into a `val`, are correct. The same
`cumulative + (if glyph_advance > 0: glyph_advance as i64 else: ...)` pattern
returns 3 in a loop (`multi=9` for three iterations instead of `21600`).

## Observed damage

`FontRenderer.measure_text_advances`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`, the cache-miss branch
`cumulative = cumulative + (if glyph_advance > 0: glyph_advance as i64 else: ...)`)
adds 3 milli-pixels instead of the glyph advance on every advance-cache miss,
so under JIT `resolve_font_metrics_with_language("Noto Sans Mono", "Overview", 12, "")`
returns advances `[0 0 0 0 7 0 7 0]` (width 14) instead of `[7 7 8 7 7 7 7 8]`
(width 58). The 2D showcase (`src/app/ui_showcase/hosts/main_2d.spl`, 1280x720)
then renders all menu labels piled at x=0 and drops the right panel, probe pane
and status bar.

macOS never showed this because large JIT modules there always panicked into
the interpreter (see
`jit_macos_arm64_code_arena_linux_only_large_runs_interpreted_2026-10-04.md`).
Any change that lets such a module JIT (smaller code, the macOS arena) makes it
visible; on Linux, where the arena already works, JIT'd UI runs are exposed today.

## Root cause (FIXED 2026-10-04)

The problem is in the parser, not the JIT. The seed parser read
`if c: x as i64 else: 5` as `if c: (x as i64 else: 5)`, which is the
`CastElse` lazy-fallback form (`expr as T else: fn`). That left the `if`
with **no else branch**. The interpreter then returned nil on the false
path (`nil is forbidden by the non-optional return contract`), and the JIT
used the constants 3/0. The pure-Simple parser has no `CastElse`, so the
two front ends disagreed. 48 `.spl` sites use this shape (for example
`src/lib/skia/feature/glyph/subpixel.spl:33`), and no `.spl` site uses
`CastElse` on purpose.

Fix: `Parser::inline_if_then_call_depth`
(`src/compiler_rust/parser/src/parser_impl/core.rs`) is set while
`parse_if_expr` parses an inline then-branch
(`expressions/helpers.rs`). At that call depth, `expressions/postfix.rs`
leaves `else:` to the `if`. `CastElse` is unchanged everywhere else,
including inside a call argument within the then-branch.

Specs (`src/compiler_rust/parser/src/if_expr_cast_else_test.rs`):
- the exact repro: `inline_if_then_cast_keeps_the_if_else`
- generalization tests:
  - `parenthesised_multiline_if_then_cast_keeps_the_if_else`
  - `else_branch_cast_is_unchanged`
  - `cast_else_outside_an_if_is_unchanged`
  - `cast_else_in_a_call_argument_inside_the_then_branch_is_unchanged`

Before the fix, the two repro tests fail (parser suite 1227 passed / 7 failed).
After the fix, the suite is 1229 passed / 5 failed; the 5 are pre-existing,
the same set as before. The probe now prints `7200 5 5` under both the JIT
and the interpreter.
