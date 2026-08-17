## FIXED 2026-08-17

Root cause, both in the Rust seed parser:
`expressions/binary.rs` `parse_unary` matched `TokenKind::Move` unconditionally
and consumed the next token as the move operand — so `move + 1u32` tried to
parse `+` as an expression. `expressions/primary/mod.rs` additionally routed a
bare `Move` into `parse_primary_lambda`, which demands a following `\`.
`primary/identifiers.rs:152` had ALREADY handled `Move` as an identifier; it was
simply unreachable.

Both sites now check the following token first (`move_is_keyword_prefix` in
`parser_helpers.rs`: lambda introducer, identifier, or `me`). A bare `move`
falls through to `parse_primary_identifier`. A census over `src/`, `test/` and
`examples/` found **zero** real unary-move or move-closure uses, so the
contextual rule is conservative.

Evidence: the pre-fix binary fails the minimal repro with the exact
`expected expression, found Plus`; the rebuilt seed prints `N=2`. Spec
`test/01_unit/compiler/parser_move_contextual_keyword_spec.spl` 4/4 (including a
scenario proving `move \x: x + 1` still parses as a move-closure).
`cargo test -p simple-parser` 281+ tests, 0 failed.

The workaround rename in `draw_ir_packed_generation_store_v3.spl` is left as-is
(cosmetic; `shift` is the better name).

## Re-verified 2026-08-17 — STILL OPEN (superseded by the note above)

Minimal repro (`var move = 3u32` then `while move + 1u32 < 10u32:`) still fails:
```
error: compile failed: parse: Unexpected token: expected expression, found Plus
```
Same defect class as `pub`/`examples`: a reserved token rejected at the USE
site. Blocker: the fix is in the Rust seed lexer/parser
(`src/compiler_rust/parser/src/expressions/helpers.rs` family) and cannot be
verified without a seed rebuild + redeploy.

# `move` identifier rejected in expression position ("expected expression, found Plus")

- **Date:** 2026-08-15
- Status: RESOLVED 2026-08-17 (was OPEN) — contextual `move` fix present: src/compiler_rust/parser/src/parser_helpers.rs:206, expressions/binary.rs:479, expressions/primary/mod.rs:158-159
- **Component:** parser (Rust seed lexer/parser reserved-word handling)

## Symptom

`src/lib/common/mission_critical/draw_ir_packed_generation_store_v3.spl` failed to
parse with `Unexpected token: expected expression, found Plus`, silently breaking
every spec that transitively imports `common.ui.draw_ir` (all engine2d draw_ir
specs went 0-passed with 0% coverage of `draw_ir_adv.spl`).

## Root cause

A local variable named `move` cannot be used in expression position:

```
var move = found.to_u32()
while move + 1u32 < self.queue_len:   # <- "expected expression, found Plus"
```

Bisection (head -n N + parse) pinned the failure to the `while move + 1u32` line;
renaming the variable to `shift` resolves it. `move` behaves as a reserved token
in expression position even though its declaration (`var move = ...`) is
accepted — same defect family as `examples`/`and_then` named-argument rejection
(see `examples_identifier_rejected_in_named_argument_position_2026-08-10.md`).

## Workaround / fix applied

Renamed the compaction cursor `move` -> `shift` in
`src/lib/common/mission_critical/draw_ir_packed_generation_store_v3.spl`
(release() queue-compaction loop, ~line 285).

## Unblock condition

Either make `move` a plain identifier, or reject its declaration with a clear
"reserved keyword" diagnostic instead of failing at the first later use, and add
`move` to the documented reserved-keyword list in `.claude/rules/language.md`.

---

## RESOLVED for the whole CLASS (2026-08-17, verified by executed tests)

`move` itself was already fixed before today (`parser_helpers.rs`
`move_is_keyword_prefix`). What was NOT fixed is that **eleven sibling soft
keywords had exactly the same defect**, each failing with a *different* error
message — which is why they were never recognised as one bug. Found by the
class-detection test `every_bindable_soft_keyword_reads_back_in_ordinary_
expression_positions`, not by any per-keyword report.

RED before (executed, `cargo test -p simple-parser --test
contextual_keyword_identifiers`):
`test result: FAILED. 2 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out`
first offender `var spawn = 3 / let a = spawn + 1` ->
`expected expression, found Plus`.

GREEN after:
`test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`

Full `cargo test -p simple-parser --no-fail-fast`: every integration suite
passes. The 4 remaining `--lib` failures are all `lexer::tests` f-string
brace-escape and are **pre-existing** — proven by re-running `--lib` with these
four files stashed: identical `277 passed; 4 failed`.

### Three distinct root-cause sites, one class

1. `parser/src/expressions/primary/mod.rs:267` — `TokenKind::Spawn` routed
   unconditionally to `parse_primary_control` -> `parse_spawn_expr`
   (`expressions/primary/control.rs:182`), which advances and parses an operand,
   so `spawn + 1` read `+` as the operand start. Now guarded by
   `soft_keyword_prefixes_operand()`; `(` is deliberately excluded so `spawn(x)`
   stays a call on an identifier.
2. `parser/src/parser_impl/core.rs:439` — new `soft_kw_stmt_as_ident` flag,
   mirroring the existing `is_return_as_ident` idiom. Covers `Skip`, `Bind`,
   `On`, `With`, `Use`, `Export`, `Requires`, `Auto`, `Mod`, `Examples`,
   `AndThen`: `<kw> =` / `<kw>.` at statement level is a variable use, never the
   statement form.
3. `parser/src/parser_patterns.rs` — the binding side had no pattern arm for
   `into`, `bind`, `unwrap`, `on`, `with`, `use`, `export`, `auto`, `where`,
   `onto`, `and_then`, so `var into = 3` died with `expected pattern, found
   Into` before any use was even reached.

`parser_helpers.rs` gained `soft_keyword_prefixes_operand()`; the pre-existing
`move_is_keyword_prefix()` now delegates to it (behaviour unchanged).

### Does NOT reproduce — the `new` claim is stale
`val new = 5 / let a = new + 1` and `var new = 0 / new = new + 1` both parse
today (probed directly against the parser crate). `error_recovery.rs:376-406`'s
`TokenKind::New` heuristic is not on that path.
