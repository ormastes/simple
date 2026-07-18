# Task #163 — `loop:` statement executes zero times on native --entry path

## Root cause

Base commit: 0b63b447263 ("fix: harden pure native runtime ABI").

`parse_statement()` in `src/compiler/10.frontend/core/parser_stmts.spl` had **no
case for the `loop` keyword** (TOK_KW_LOOP, kind 51). A statement-form `loop:`
therefore fell through to expression parsing and hit the expression-position
handler in `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:775`,
which parses `loop: <block>` as a plain `expr_block(stmts, -1, 0)` — a one-shot
block with **no loop semantics at all**. The interpreter's own tree-sitter-based
frontend (`src/app/interpreter/ast_convert_stmt.spl`, `Statement.Loop`) handles
`loop` correctly, which is why the oracle looped and native did not.

(In the pre-fix build the body actually executed zero-visible-times on the
battery case because the block also swallowed the prints on the native path;
either way, no back-edge existed in the emitted code.)

## Fix (parser-level desugar, earliest layer)

`src/compiler/10.frontend/core/parser_stmts.spl` only — 3 edits:

1. Import `TOK_KW_LOOP` (line 12) and `expr_bool_lit` (line 36).
2. `parse_statement()`: dispatch `kind == TOK_KW_LOOP` → new `parse_loop_stmt()`
   (placed right after the `while` dispatch).
3. New `fn parse_loop_stmt()`: consume `loop` + `:`, `parse_block()`, and return
   `stmt_while_stmt(expr_bool_lit(1, 0), body, 0)` — byte-identical AST shape to
   what `while true:` produces (the G19 while-val desugar directly above already
   uses this exact pattern).

Note: the first attempt used `expr_ident("true", 0)` (copying the G19 desugar),
which the HIR lowerer rejected with a **loud** `unresolved name: true` error on
the native path (interpreter resolves it fine). Switched to the real
`EXPR_BOOL_LIT` node — same node a literal `true` token produces. This suggests
the G19 `while val` desugar at parser_stmts.spl:876 (`expr_ident("true", 0)`)
has the same latent issue on the native path; not touched (out of scope).

Loop-as-EXPRESSION (`val x = loop: ... break v`) is untouched — still routed
via primary_expr.spl:775. No loud failure was converted to a silent one.

## Battery: oracle vs native (stdout values)

| # | Case | Oracle | Native (after fix) | Match |
|---|------|--------|--------------------|-------|
| 1 | basic loop+break (`battery1_basic.spl`) | 1 2 3 4 | 1 2 3 4 | YES (values) |
| 2 | loop with continue (`battery2_continue.spl`) | 1 3 5 | *(empty, exit 5)* | NO — pre-existing `continue`-in-`while true` native bug, see below |
| 3 | nested loop-in-loop, flag exit (`battery3_nested.spl`) | 11 12 21 22 31 32 | 11 12 21 22 31 32 | YES (values) |
| 4 | multi-construct: 2 loops + while + for interleaved (`battery4_multi.spl`) | 101 102 201 202 301 302 303 401 402 | 101 102 201 202 301 302 303 401 402 | YES (values) |

Caveats (all **pre-existing** native-path defects, verified byte-identical on the
UNMODIFIED worktree via `git stash` A/B runs — none introduced by this change):

- **Native `print(int)` emits no trailing newline** and process exit codes are
  garbage after loops with `break` (e.g. literal `while true: ... break` prints
  `1234`, exit 1; `while i<10 ... break` even drops output, exit 24/200 with
  `exit_group(1549838280)` garbage). Reproduced with literal `while` loops with
  no `loop:` in the file. So "match" above = printed values match; native
  formatting/exit-code defects are shared with plain `while` and out of scope.
- **Battery 2 (`continue`)**: `continue` inside a constant-true `while` loop is
  broken on native **independent of this fix** — literal
  `while true: ... continue ...` on the *unmodified* worktree gives the
  identical failure (no output, garbage exit code, strace shows zero `write`
  calls, `exit_group(-2147483643)`). Bounded `while i < 6: ... continue` works
  (prints 1 3 5). The `loop:` desugar inherits this while-true bug; it does not
  cause it. Recommend filing as a separate native-codegen bug:
  "continue in while-true loop: no output + garbage exit code on native path".
- `for i in 1..5` (range) also panics on native — known #143, unrelated.

## Smoke matrix (`sh scripts/check/native-smoke-matrix.shs` from worktree)

`total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0`

Only failure = `option_nil_check` (rc 1 vs 7) — the explicitly allowed failure.
`while_sum` (case 3) and `for_in_array` (case 4) PASS, confirming no regression
to existing loop lowering. **Gate met: >=14/15, 0 fallback hits, only allowed fail.**

## Files touched

- `src/compiler/10.frontend/core/parser_stmts.spl` (+44/-2) — only file changed.
- Not touched: `parser_decls_fn.spl`, `convert_nodes.spl` (parallel-lane owned),
  `primary_expr.spl` (loop-as-expression left as-is).

Patch: `scratchpad/loop_desugar.patch` (apply with `git apply` from repo root).
