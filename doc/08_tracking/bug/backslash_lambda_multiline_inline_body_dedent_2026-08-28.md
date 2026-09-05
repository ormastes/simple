# Seed parser: backslash-lambda inline body with a trailing-operator continuation fails "found Dedent"

**Status:** FIXED (parser fix landed in this lane's worktree; not yet merged to main)
**Date:** 2026-08-28
**Component:** `src/compiler_rust/parser` (Rust bootstrap seed parser)

## Summary

`bin/simple run` (Rust seed) failed to parse a `\arg: expr` backslash-lambda
(and the `fn(arg): expr` lambda spelling) whenever:

1. the lambda body is an **inline expression** (starts on the same source
   line as the colon, not on a new indented line), **and**
2. that expression **continues onto a later line** via a trailing binary
   operator (`and`, `or`, ...), **and**
3. the lambda itself is a **call argument** (e.g. `.any(\row: ...)`), which is
   exactly when the parser's "forced indentation" machinery is active.

Symptom: `error: compile failed: parse: ... Unexpected token: expected
expression, found Dedent`.

This is the root cause (or one of two root causes — see "Known related but
distinct defect" below) of the ~66+17 spec/compiler-source parse failures
recorded in `$S/coverage_wrapper_fix_REPORT.md` under
`src/compiler/50.mir/hwir/riscv_scalar_*`, which use this exact shape
extensively, e.g.
`test/01_unit/compiler/50.mir/hwir_riscv_scalar_runtime_lsu_composition_spec.spl:17-38`
(as it existed in the `phase1-iso` worktree — this file has since been
removed/relocated on `main`).

## Minimal repro

```
fn main():
    val rows = [1, 2]
    val x = rows.any(\row: row == 1 and
        row == 2)
    print(x)
```

Also saved at `$S`-adjacent scratch: originally isolated at
`/mnt/data/tmp/seed-parser-fix-wt/scratch_repro/min4.spl` by bisecting the
70-line original spec (`min1..min9.spl` in the same directory record each
narrowing step: the trigger needs a call-argument context, NOT just `val f =
\row: ...`, which parses fine — see `min6.spl`/`min7.spl` controls).

## Root cause

Two lambda-parsing entry points implement the exact same three-way body shape
(block / inline-after-newline / **inline-same-line**) and both had the
timing bug only in the third branch:

- `parser/src/expressions/helpers.rs::parse_lambda_body` (used by
  `\arg: expr` and `move \arg: expr`)
- `parser/src/expressions/primary/lambdas.rs::parse_primary_lambda`'s
  `TokenKind::Fn` arm (used by `fn(arg): expr`)

Both call `self.lexer.enable_forced_indentation()` before consuming the `:`,
so that a genuine block body (colon, newline, indent) gets real
`Indent`/`Dedent` tokens even though the lambda sits inside call-argument
parentheses (where the lexer normally suppresses significant
newlines/indentation by bracket depth). That part is correct and by design.

The bug is in the **inline-expression** branch (colon is *not* followed by a
`Newline` — body starts right there on the same line):

```rust
} else {
    // Inline expression - disable forced indentation after parsing
    let expr = self.parse_expression()?;
    self.lexer.disable_forced_indentation();   // <-- too late
    expr
};
```

`disable_forced_indentation()` runs **after** `parse_expression()` returns —
but `parse_expression()` is exactly what consumes the continuation line(s)
when the expression ends in a trailing binary operator. With forced
indentation still enabled while that continuation line is lexed, the lexer
emits a real `Indent`/`Dedent` pair for it (because forced indentation
defeats the normal bracket-depth newline suppression), which
`parse_expression()`'s binary-operator continuation logic does not expect and
cannot consume. Parsing fails once it reaches the (now doubly-orphaned)
`Dedent` token — trying to parse it as the start of the next operand,
producing "expected expression, found Dedent".

The single-line-body case (no continuation) never triggers this because
`parse_expression()` returns without crossing a line boundary, so no
Indent/Dedent tokens are ever emitted for it in the first place — masking the
bug for the common case and letting it survive.

## Fix

Move `disable_forced_indentation()` to **before** `parse_expression()` in
both inline-expression branches, matching the ordering already used
correctly in the sibling "just a newline, parse next expression" branch a few
lines above in the same functions. Once forced indentation is off, an inline
body's continuation line is lexed under ordinary bracket-depth suppression
(same as any other expression inside `(...)`), which already handles
multi-line continuations correctly — this is the same mechanism the
`trailing_operator_single_line_body_test.rs` regression suite (2026-07-13
bug) already exercises for `if`/`while` conditions.

Files changed:
- `src/compiler_rust/parser/src/expressions/helpers.rs` (`parse_lambda_body`)
- `src/compiler_rust/parser/src/expressions/primary/lambdas.rs`
  (`parse_primary_lambda`, `Fn` arm)

## Evidence

- New regression suite `parser/src/lambda_multiline_inline_body_test.rs` (11
  cases: 8 that failed pre-fix across all four lambda spellings —
  `\x:`, `move \x:`, `fn(x):`, and a nested-lambda case — covering `and`,
  `or`, two-param lambdas, trailing-comma-before-close, and nesting; plus 3
  controls that already passed and must keep passing: single-line body,
  genuine block body, and a plain non-call-argument `val f = \x: ...`
  continuation).
  - Confirmed RED pre-fix: `git stash` the two source files, same test
    filter → `8 failed, 3 passed` (exact predicted split).
  - Confirmed GREEN post-fix: `11 passed, 0 failed`.
- `cargo check --release --bin simple`: clean.
- Full seed binary rebuilt in the lane worktree
  (`/mnt/data/tmp/seed-parser-fix-wt`); see the lane report for `run`-level
  verification against the minimized repro and named specs from the original
  triage report.

## Known related but distinct defect (NOT fixed by this change)

`src/compiler/50.mir/hwir/riscv_scalar_fence_owner.spl` (imported by
`hwir_riscv_scalar_fence_owner_spec.spl`) still fails to parse after this fix,
with the same "found Dedent" message, but it contains **no backslash lambdas
at all** (`grep -c '\\\\'` = 0). Its trigger is a **different** construct: an
inline `if`/`else` **expression** (not lambda) whose **condition** continues
onto a later line before the colon:

```
val output_name = if field[0] == "event_id" or field[0] == "decode_event_id" or
    field[0] == "illegal_valid": "completion_" + field[0] else: field[0]
```

Minimized repro:
```
fn main():
    val x = if 1 == 1 or
        1 == 2: "a" else: "b"
    print(x)
```

This lives in `parse_if_expr` (`expressions/helpers.rs`), which already has a
partial fix for a sibling shape (`drain_available_deferred_dedents()` at line
205, guarding the block-form `if cond:\n    body` case per the 2026-07-13
trailing-operator bug) but not this inline-`if`-as-expression-with-multiline-
condition shape — a block-form variant of the same minimized condition
(`min10.spl` in the scratch dir) fails differently ("expected Indent, found
FString"), showing the existing drain logic is not sufficient here either.
This needs its own investigation and is out of scope for this lane (scoped to
the lambda-inline-body defect); filing it here so it is not lost. No parser
fix attempted for this second defect — recorded, not fixed, per this lane's
scope.

## Verification against the original triage report's named specs

Run from `/mnt/data/worktrees/phase1-iso` (where the report's exact named
files still exist) using the rebuilt seed binary from this lane's worktree:

| spec | before | after |
|---|---|---|
| `hwir_riscv_scalar_runtime_lsu_composition_spec.spl` | parse: found Dedent | parses past the Dedent point; now fails at an unrelated pre-existing `cannot resolve import` error (module-path resolution, not parsing) |
| `hwir_riscv_scalar_decoder_spec.spl` | parse: found Dedent | same as above — parses past Dedent, then the same unrelated import-resolution error |
| `hwir_riscv_scalar_fence_owner_spec.spl` | parse: found Dedent | still `found Dedent` — blocked by the distinct if-expression defect above, not this fix's target |

The import-resolution error is unrelated to parsing (it is an `E1034` module
path lookup failure against the `phase1-iso` worktree's own layout) and is
out of scope here.

## Follow-up: second defect RESOLVED (2026-08-28, later same day)

The "known related but distinct defect" above (inline `if`/`else`
**expression** whose **condition** trails a binary operator onto a later
line before the colon) is now fixed. It turned out to be **two** separate
gaps in `parse_if_expr` (`expressions/helpers.rs`), both absent from the
sibling statement-form `if` (`parse_if`, `stmt_parsing/control_flow.rs`),
which already handled both shapes correctly:

### Gap 1 — inline then/else branches never reconciled the condition's deferred dedent

`parse_if_expr`'s INLINE then-branch and INLINE else-branch (`if cond: a
else: b`) parsed their expression bodies and moved on without ever calling
`reconcile_inline_body_deferred_dedents()` — the statement-form `if`
(`parse_inline_or_block`) and every other inline body (elif/else/match-arm)
already call it. A multi-line condition's trailing-operator continuation
(`if 1 == 1 or\n    1 == 2: "a" else: "b"`) leaves a compensating pseudo-
DEDENT queued in `deferred_dedent_count`; with no reconcile call it leaked
into whatever token followed the whole if-expression and surfaced as an
orphaned `found Dedent` there. Fix: call
`self.reconcile_inline_body_deferred_dedents()` right after parsing BOTH the
inline then-branch expression and the inline else-branch expression (both
needed — a `then` followed immediately by `else:` on the same line never
gives the first reconcile call anything to consume, so the pending dedent
survives to the point right after the else-branch and must be reconciled
again there).

### Gap 2 — block-form then-branch didn't handle the equal-column continuation shape

Even after Gap 1, the BLOCK-form then-branch (`if <cond>:\n    body`, with
the condition's continuation column equal to the body's column) still failed
with "expected Indent, found `<first body token>`". In this shape the lexer
emits no fresh `Indent` for the body at all — the continuation's own
pseudo-INDENT already opened that level — so a bare `self.expect(&TokenKind
::Indent)?` fails outright. The statement-form `if` already has a dedicated
mechanism for exactly this ("equal-column shape") in `parse_condition_block`
(`parser_impl/core.rs`), built on `header_continuation_is_equal_column` /
`header_continuation_dedents_to_reconcile`
(`parser_helpers.rs`,
doc/08_tracking/bug/parser_while_continuation_swallows_following_declarations_2026-08-01.md)
— but `parse_if_expr`'s hand-rolled block-body loop never used it. Fix:
`parse_if_expr`'s block-form then-branch now calls
`header_continuation_is_equal_column` before deciding whether to
`expect(Indent)`, and after the block body applies the same
`saturating_sub(1)` reconciliation `header_continuation_dedents_to_reconcile`
uses, since in the equal-column shape the body's own terminating `Dedent` IS
the continuation's compensating one and must not be counted twice.

### Gap 3 (found while fixing Gap 2) — `is_statement_start()` didn't recognise literal/expression-start tokens

Fixing Gap 2 exposed a THIRD, more general pre-existing gap:
`header_continuation_is_equal_column` decides "is this the flat/no-Indent
body start" via `is_statement_start()`, which is missing most
literal/expression-start token kinds (`FString`, `String`, `Integer`,
`Float`, `Bool`, `Nil`, `LParen`, `LBracket`, unary `-`/`not`, `\` lambda —
only identifiers, `self`, `_`, and statement keywords were covered). A block
body whose first (and possibly only) statement is a bare expression starting
with one of these — e.g. `riscv_scalar_csr_owner.spl`'s
`"completion_" + field[0]` — still hit `expect(Indent)` and failed with
"expected Indent, found FString(...)". This is the SAME category of gap the
2026-08-26 `Self_`/`Underscore` addition to this same function already
documents (see the comment directly above the new entries in
`is_statement_start`, `parser_impl/core.rs`) — just for literal tokens
instead of `self`. Fix: added the literal/expression-start `TokenKind`
variants listed above to `is_statement_start()`. This is shared by
`if`/`elif`/`while`/`for`/match-arm-guard equal-column detection AND the
flat-body path in `parse_block_after_newline`, so it fixes the same class of
defect everywhere `is_statement_start()` is consulted, not just in
`parse_if_expr`.

### Files changed
- `src/compiler_rust/parser/src/expressions/helpers.rs` (`parse_if_expr`):
  Gap 1 (both inline branches) and Gap 2 (block-form then-branch).
- `src/compiler_rust/parser/src/parser_impl/core.rs` (`is_statement_start`):
  Gap 3.
- New test file `src/compiler_rust/parser/src/if_expr_multiline_condition_test.rs`
  (15 cases, registered in `parser/src/lib.rs`): 5 inline-both-branches
  shapes (Gap 1), 3 block-form equal-column shapes (Gap 2/3, including the
  exact `riscv_scalar_csr_owner.spl` shape and a multi-statement body), 2
  neighbor controls (`while`/`match`-guard multi-line conditions, must not
  regress), and 5 controls (single-line condition, parenthesized
  continuation, existing block-form multi-line condition, call-argument
  position, the `riscv_scalar_fence_owner.spl` inline shape).
  - Confirmed RED pre-fix (Gap 1+2 reverted): 5 of 11 originally-written
    inline/block cases failed exactly as predicted.
  - Confirmed GREEN post-fix (all three gaps fixed): all 15 cases pass;
    `cargo test -p simple-parser --release` — 343 passed (up from 340), 0
    newly failed; the one pre-existing failure
    (`ts_arrow_detection_rule_was_retired_when_the_arrow_lambda_landed`, in
    `parser/tests/control_flow.rs`, untouched by this change) is unrelated.
- `cargo check --release --bin simple`: clean.

### `run`-level verification (rebuilt seed binary, this worktree)
- `src/compiler/50.mir/hwir/riscv_scalar_fence_owner.spl` and
  `src/compiler/50.mir/hwir/riscv_scalar_csr_owner.spl`: both now parse past
  the point that used to fail with "found Dedent" / "expected Indent, found
  FString"; each now stops at an unrelated pre-existing semantic error
  (`undefined identifier: _bi_bytes_to_hex`) or resolves cleanly — parsing
  itself is no longer the blocker for either file.
- `test/01_unit/compiler/50.mir/hwir_riscv_scalar_fence_owner_spec.spl` (run
  from `/mnt/data/worktrees/phase1-iso` with the rebuilt seed binary): no
  longer errors out during compilation at all — the test runner now executes
  the whole spec and reports `Results: 4 total, 2 passed, 2 failed`. The 2
  failures are genuine test-assertion failures ("makes FENCE.I an explicit
  instruction-stream invalidation effect", "emits and composes one stateful
  fence provider with no completion skid") — logic-level gaps unrelated to
  parsing, out of scope for this parser fix.

No commit/push/deploy performed as part of this follow-up.
