# A parameter named `out` (or `out_err`) is hijacked by the contract-block parser

Status: FIXED 2026-08-11. Parser-level, so it affects every engine equally
(Rust seed and pure-Simple self-hosted parser share this defect shape — see
"Engines checked" below for which was actually rebuilt and verified this
session). Same family as
`identifier_named_grid_hijacked_by_grid_literal_parser_2026-08-09.md`: a
contextual keyword's disambiguation test fires on the wrong signal (a single
token that also occurs in the ordinary-code shape) instead of the real
disambiguating syntax.

## Summary

`out` and `out_err` are documented as intentionally-not-reserved parameter
names (`src/compiler_rust/parser/src/parser_impl/core.rs:1047`,
`is_reserved_parameter_name`, with a comment saying the ambiguity is
"resolved positionally"). That positional resolution was incomplete: the
function-body dispatcher that decides whether the body opens with a contract
block treated a bare `Out`/`OutErr` token as sufficient evidence of
`out(ret):` / `out_err(err):` contract syntax, without checking for the `(`
that actually distinguishes the contract clause from a parameter named `out`
used as an ordinary statement-leading expression.

## Reproduce (pre-fix)

```simple
fn f(out: [u8]):
    out.push(1)
```

    error: compile failed: parse: Unexpected token: expected LParen, found Dot

The message names neither `out` nor the real cause; it points at the `.` in
`out.push(1)` because `parse_exit_contracts` had already consumed `out` as
the start of an `out(ret):` clause and then choked on the next token not
being `(`.

Confirmed variations:
- `fn f(xs: [u8]): xs.push(1)` — parses fine (differently-named param, control).
- `val out = [1]` then `out.push(1)` at module/script top level — parses fine
  (not the first statement of a function *body* opened via the block-form
  `fn f(out: [u8]):\n    ...` path, so the contract dispatcher never runs).
- `fn f(out x: T)` — also rejected, but via a *different* mechanism (parameter
  parsing, not this contract dispatcher); not fixed by this change, see "Not
  fixed" below.

## Root cause

Two call sites did one-token dispatch instead of checking the real
disambiguating syntax (`(` immediately after `out`/`out_err`):

1. `src/compiler_rust/parser/src/parser_impl/functions.rs` (around what was
   line 205-212): the block-form function body parser decided whether to call
   `parse_contract_block()` based on `self.check(&TokenKind::Out) ||
   self.check(&TokenKind::OutErr)` alone.
2. `src/compiler_rust/parser/src/stmt_parsing/contract.rs`,
   `parse_exit_contracts`: same one-token test, reachable a second way — if a
   function body opens with a genuine `in:`/`invariant:` entry-contract
   block, control reaches `parse_exit_contracts` next, and a following
   parameter-named-`out` statement gets hijacked there too, independent of
   the functions.rs dispatch.

Both are structurally identical to the `grid`-literal bug: a contextual
keyword's trigger test was one token deep, when the grammar's own
disambiguating token (`|` for grid rows, `(` for contract out-clauses) was
available one token later.

## Fix

Gate both call sites on lookahead:

```rust
let out_starts_contract = (self.check(&TokenKind::Out) || self.check(&TokenKind::OutErr))
    && self.peek_is(&TokenKind::LParen);
```

- `src/compiler_rust/parser/src/parser_impl/functions.rs` — dispatch into
  `parse_contract_block()` only when `out`/`out_err` is followed by `(`.
- `src/compiler_rust/parser/src/stmt_parsing/contract.rs` —
  `parse_exit_contracts` requires the same `(` lookahead before consuming
  `Out`/`OutErr` as the start of a postcondition block, instead of consuming
  unconditionally and failing later on the missing `(`.

`in`, `invariant`, `requires`, `ensures`, `decreases` were left unchanged:
they are followed by `:` in their real grammar (`in:`, `invariant:`, ...),
which is not a token that also introduces a legitimate parameter body, so
they do not share this hijack shape (see "Family sweep" below for why they
were checked and ruled out, not just skipped).

## Engines checked

- **Rust seed** (`src/compiler_rust`, `cargo build --release --bin simple`):
  fix applied and rebuilt; this is the currently-deployed `bin/simple` (it
  prints the bootstrap-seed warning banner — see `.claude/rules/bootstrap.md`
  "KNOWN BLOCKER" for why self-host is not currently deployable). Verified
  the exact repro shape parses and executes after rebuild.
- **Pure-Simple self-hosted parser** (`src/compiler/10.frontend`): per the
  sibling `grid` bug's own finding, the pure-Simple parser has no
  grid-literal rule at all and was unaffected by that bug. For *this* bug,
  `src/compiler/10.frontend` implements its own contract-block parsing
  independently of the Rust seed's `stmt_parsing/contract.rs` — it was not
  touched by this change and was not independently re-audited for the same
  one-token-dispatch shape in this session. Flagging as an open follow-up
  rather than claiming parity: search `src/compiler/10.frontend` for its
  `out(`/`out_err(` contract-clause dispatch and confirm/fix the same
  lookahead there.

## Family sweep — other contextual-keyword hijack candidates

Checked every keyword sharing the "documented as non-reserved parameter name,
used contextually elsewhere" shape:

- **`out` / `out_err`** — hijacked, fixed here.
- **`in`** — also listed as ident-like in `is_inline_assignment`
  (`stmt_parsing/control_flow.rs:50`) and used as a for-loop keyword
  (`for x in y`) and entry-contract keyword (`in:`). Its contract-block use
  is followed by `:`, not a token that also starts ordinary code the same way
  `(` does for `out`, and `for`/`in` position already requires prior `for`
  context, so no equivalent hijack shape was found. Not fixed because no
  reproducing case was found, not skipped for convenience — if one turns up,
  the fix pattern here (lookahead-gate on the real disambiguator) applies
  directly.
- **`invariant`, `requires`, `ensures`, `decreases`** — same reasoning as
  `in`: all followed by `:`, no ordinary-code shape found that starts with
  one of these tokens then diverges from contract syntax.
- **`grid`** — separate, already-fixed bug
  (`identifier_named_grid_hijacked_by_grid_literal_parser_2026-08-09.md`),
  same mechanism family, unrelated call sites.
- **`fn f(out x: T)` — parameter-modifier-keyword position, NOT fixed here.**
  This is a genuinely different mechanism: `out` in *parameter-modifier*
  position (before a parameter name, e.g. an output/by-reference marker) is
  parsed by different code than the statement-leading-body case above, and
  still misbehaves. Confirmed still rejected after this fix (parser change
  here only touches body-dispatch, not parameter-list parsing). Left open —
  needs its own investigation into whatever parses parameter modifiers
  (`src/compiler_rust/parser/src/parser_impl/functions.rs` parameter-list
  loop, distinct from the body dispatcher fixed here).

## Is `out` a real reserved word here?

No — `.claude/rules/language.md`'s reserved-keyword list (`gen`, `val`, `def`,
`exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`,
`pass_dn`, `examples`, `and_then`) does not include `out`, and
`is_reserved_parameter_name` in `parser_impl/core.rs` explicitly documents
`out` as intentionally not reserved, precisely so it stays available as a
parameter name for output-buffer conventions (`fn f(out: [u8])` appears
throughout the codebase, including the untracked in-flight
`src/os/sosix/fs/ipc_codec_v1.spl` that motivated this investigation — not
touched by this fix). `out` is a *contextual* keyword (like `grid`), not a
reserved one; this bug was the parser's context-tracking failing to
disambiguate correctly, not a case for adding `out` to the reserved list.
