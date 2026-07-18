# Task #163 remainder — loop-as-expression `break <value>` (native --entry)

Worktree: /tmp/wt_brkval @ f10db44f0f4 (detached). Compiler edits are interpreted
by `bin/simple native-build`, so no rebuild was needed.

## Characterization (pre-fix, on base f10db44f0f4)

| # | Probe | Oracle (`bin/simple run`) | Native (`native-build --entry`) |
|---|-------|---------------------------|----------------------------------|
| 1 | `val x = loop:\n    break 5\nprint(x)` (expression form) | BROKEN — "HIR lowering error: Unknown variable: loop", then `error[E1002]: function 'loop' not found`, exit 0 (!) — no reliable oracle, as pre-briefed | builds OK, prints `0` — SILENT WRONG (the bug) |
| 2 | `var x = 0; loop: x = 41; break; print(x)` (statement form, landed desugar) | prints `41` | prints `41` — works |
| 3 | grammar | `val x = loop:` IS accepted by the parser (no parse error) — falls into `_ParserPrimary/primary_expr.spl` kind==51 branch | same |

Findings on the three characterization questions:
1. **Parse accepted?** Yes — `loop` in expression position hits the kind==51 branch of
   `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`, which wrapped the body
   in a plain one-shot `expr_block(body, -1, 0)`: no loop back-edge, no result value.
2. **Does `break 5` parse the value?** No. The only break parse in
   `src/compiler/10.frontend/core/parser_stmts.spl` (kind==47, line ~394) handles bare
   `break` and labeled `break 'label`; there is NO value operand anywhere —
   `stmt_break_stmt(span)` (ast_stmt.spl:320) carries no payload field. The `5` is
   dropped at parse. (Inside an indented block the `5` lands on the same line; it is
   simply never consumed as part of the break.)
3. **What reaches HIR/MIR?** A one-shot EXPR_BLOCK with a bare STMT_BREAK inside and
   block value = -1 → block evaluates to 0/nil; native path prints 0. Interpreter path
   is differently broken (treats `loop` as a call target). So the form is broken
   end-to-end: parse drops the value, AST has no loop node, no break-value channel in
   HIR/MIR.

## Outcome chosen: LOUD parse error

The form is broken end-to-end (no value in AST, no loop semantics, no HIR/MIR channel,
and no working oracle to verify an implementation against). Per scope rules the smallest
sound outcome is to convert the silent-0 into a fatal parse error.

Change: `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` kind==51 branch
now emits `parser_error("loop-as-expression with break-value is not supported ...; use a
var + statement-form loop")` (still consumes the block for recovery, returns nil-lit).
parser_error sets `par_had_error`, which the landed phase-2 gate turns into a fatal
build failure. Statement-form `loop:` is untouched — it is intercepted earlier in
`parser_stmts.spl` (kind==TOK_KW_LOOP → parse_loop_stmt desugar to while-true) and never
reaches this branch.

Repo grep: no in-tree .spl source uses `= loop:` expression form, so nothing regresses.

Oracle note: `bin/simple run` executes the Rust seed's own frontend, which .spl parser
edits do not affect; its expression-form behavior stays its pre-existing loud E1002
("function `loop` not found") — not silent, so no oracle regression either. Native-path
verification is BY CONSTRUCTION (loud fail observed empirically), as pre-authorized.

## Verification battery (post-fix)

| Probe | Expect | Got | PASS |
|-------|--------|-----|------|
| p1 `val x = loop: break 5` native-build | exit!=0, NO binary, loud message | build exit=1, `[parser_error] line 2:13: loop-as-expression with break-value is not supported...`, `[ERROR] phase 2 FAILED`, /tmp/out_p1_v2 absent | PASS |
| p2 statement-form `loop:` + break control | binary prints 41 | prints 41, build exit=0 | PASS |
| p3 plain while loop control | prints 3 | prints 3 | PASS |
| Full smoke matrix `scripts/check/native-smoke-matrix.shs` | >=14/15, 0 codegen_fallback_hits, only option_nil_check may fail | see below | (below) |

## Smoke matrix summary

Run from /tmp/wt_brkval with the fix applied (`sh scripts/check/native-smoke-matrix.shs`,
work dir /tmp/nsm_brkval, log /tmp/nsm_brkval.log):

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

Per-case: arith_fn_call PASS; if_elif_else PASS; while_sum PASS; for_in_array PASS;
array_index_rw PASS; struct_field PASS; enum_construct PASS; enum_match PASS;
string_concat_len PASS; string_interp PASS; nested_fn_3deep PASS; closure_lambda PASS;
dict_index PASS; option_nil_check FAIL (the one allowed fail); result_try_op PASS.

GATE MET: 14/15 >= 14, 0 codegen_fallback_hits, only fail is option_nil_check.

## Deliverables
- Patch: /home/ormastes/dev/pub/simple/scratchpad/break_value.patch (single-file, 30 lines)
- No commit/push. Worktree removed after.
