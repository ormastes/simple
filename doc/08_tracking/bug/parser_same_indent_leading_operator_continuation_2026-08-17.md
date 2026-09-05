# Leading-operator line continuation at the SAME indent does not parse

**Date:** 2026-08-17
**Status:** OPEN — **and the obvious one-character fix is now PROVEN UNSAFE.**
See "Why the obvious fix is wrong" below. Reproduced again 2026-08-17.
**Severity:** MEDIUM — `src/lib/nogc_async_mut/wm/wm_optimization.spl` (and every
module importing it) fails to parse
**Found by:** `src/lib/**` parse sweep (7780 files)
**Binary:** `/mnt/data/cgtw2/release/simple` (freshly built Rust seed) — also
fails on the stale deployed binary, so this is not a fresh-build regression

## Relationship to the existing record

`doc/08_tracking/bug/parser_leading_operator_line_continuation_2026-08-01.md` is
marked FIXED and its repro genuinely passes today. That fix covered the
continuation line being **more indented** than the first line. The **same-indent**
shape was never covered and still fails.

## Minimal reproduction

FAILS — continuation at the same indent as the head line:

```simple
fn a1(a: text) -> text:
    "x" + a
    + "y"
```

```
error: compile failed: parse: Unexpected token: expected expression, found Plus
```

PASSES — identical expression, continuation indented one level deeper:

```simple
fn a2(a: text) -> text:
    "x" + a
        + "y"
```

## Real-world site

`src/lib/nogc_async_mut/wm/wm_optimization.spl:55-61`:

```simple
fn dirty_rect_info(r: DirtyRect) -> text:
    "DirtyRect(sid=" + r.surface_id.to_text()
    + " x=" + r.x.to_text()
    + " y=" + r.y.to_text()
    ...
```

## Expected

A line beginning with a binary operator continues the previous expression
regardless of its indent — a line cannot start with an infix operator otherwise,
so there is no ambiguity to resolve.

## Re-verified 2026-08-17 (still fails)

Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC.

```
$ cat r2.spl
fn a1(a: text) -> text:
    "x" + a
    + "y"
fn main() -> i64:
    print("{a1("q")}\n")
    0
$ bin/simple run r2.spl
[INFO] JIT compilation failed, falling back to interpreter: module load error: parse: in ".../r2.spl": Unexpected token: expected expression, found Plus
error: compile failed: parse: in ".../r2.spl": Unexpected token: expected expression, found Plus
```

## Root cause located (pure-Simple frontend), file:line

`src/compiler/10.frontend/core/lexer_struct.spl:325-332`, `fn leading_op_continues`:

```simple
fn leading_op_continues(indent_level: i64, p: i64) -> bool:
    if not token_can_end_expr(self.cur_kind):        # guard 1
        return false
    val stack_len: i64 = self.indent_stack.len()
    val current_indent: i64 = self.indent_stack[stack_len - 1]
    if indent_level <= current_indent:               # guard 2  <-- THIS
        return false
    self.line_starts_binary_op(p)
```

Guard 2 is the exclusion. `indent_level == current_indent` is the same-indent
case and is rejected by the `<=`. Call sites: `lexer_struct.spl:1252-1256`
(Indent suppression) and `:1367-1372` (Newline suppression). The operator
recogniser is `line_starts_binary_op` at `:282`. Rust seed counterpart of the
whole mechanism is the trailing/leading continuation logic in
`src/compiler_rust/parser/src/`; the `expected expression, found Plus`
diagnostic text is the seed's (`parser/src/error.rs`).

## Why the obvious fix is wrong — DO NOT relax `<=` to `<`

The one-character change `if indent_level < current_indent` is what this row's
"Expected" section implies, and it **silently miscompiles real in-tree code.**

This row asserts "a line cannot start with an infix operator otherwise, so there
is no ambiguity to resolve." That is **false for `+` and `-`, which are also
unary**, and the ambiguity is live, not theoretical.

Counter-example, real code, found by scanning `src/**` and `test/**` for a line
starting with a binary operator at the SAME indent as the line above it —
`src/compiler/85.mdsoc/cross_query.spl:128-137`:

```simple
    if ch == "1": return 1
    ...
    if ch == "9": return 9
    -1
```

The trailing `-1` is an **implicit return** at the same indent as the statement
above it. Guard 1 does not save it: the previous token is the integer literal
`9`, which `token_can_end_expr` accepts. So with `<=` relaxed to `<`, the lexer
folds the lines into `return 9 - 1` and the function returns **8 instead of -1**
— a wrong answer with no diagnostic, in the MDSOC layer-number parser.

This is the same hazard class the guard was added for. Note that the existing
regression spec
`test/01_unit/compiler/parser_leading_operator_continuation_spec.spl` documents
negative shape #2 as an implicit return that **DEDENTS** out of a loop body
(`indent_level < current_indent`), which a `<`-relaxation preserves — so that
spec would stay GREEN while `cross_query.spl` silently broke. **The existing
test suite does not cover this hazard and would not catch the regression.**

Scan method (naive, counts docstring bullet lines too, so treat the totals as an
upper bound — the `cross_query.spl:137` hit was confirmed by reading the source):
walk `src/compiler src/lib src/app src/runtime test` for `.spl` lines whose first
non-space characters form a binary operator and whose indent equals the previous
non-blank non-comment line's indent. Ambiguous `+`/`-`-led hits dominate the
result set, which is why `+`/`-` cannot simply be waved through.

## What a real fix has to do

The defect is real and should still be fixed, but it needs a disambiguation
rule, not a relaxed comparison. Options, none implemented or measured here:

1. **Split the operator set by arity at same indent.** Permit the same-indent
   continuation only for operators that can never be unary (`*`, `/`, `%`, `<`,
   `>`, `&`, `^`, `==`, `!=`, `??`, `and`, `or`, `in`, `is`, `as`) and keep
   rejecting `+`/`-` there. Cheap and safe, but **does not fix this row's own
   repro or its real-world site** — `wm_optimization.spl:55-61` is `+`-led — so
   it is a partial fix at best.
2. **Use "is this the last statement of the block" (implicit-return position).**
   That is the actual discriminator, but it is not available in the lexer, which
   is where `leading_op_continues` lives. It would need the decision moved to
   the parser or a lookahead to the block's Dedent.
3. **Require the head line to be syntactically incomplete.** Also a parser-level
   property, not a lexer-level one.

Whoever takes this should decide between (2)/(3) and a grammar change, and must
add `cross_query.spl:137`'s shape to
`parser_leading_operator_continuation_spec.spl` as negative coverage FIRST —
the current spec does not contain it.

**No fix was applied for this row.** The `<=` at `lexer_struct.spl:330` is
unchanged, deliberately, on the evidence above.

## Not worked around

The source was deliberately left unchanged: reindenting it would erase the
repro and paper over a parser defect. Fix belongs in the frontend's
continuation handling.
