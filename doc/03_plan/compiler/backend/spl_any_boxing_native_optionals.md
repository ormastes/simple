# Task: `.spl` native primitive-boxing (`any`-tagging) + typed-optional support

**Status:** OPEN (tracked) — created 2026-06-25
**Domain/topic:** compiler / backend (self-hosted `.spl` MIR + native/JIT codegen)
**Priority:** medium — correctness gap, currently produces silently-wrong output
**Related:** `doc/08_tracking/bug/interp_typed_optional_nil_field_access_sigsegv_2026-06-25.md`
(full root-cause, validated seed design, and workflow `wf_81e1ad20-5aa` findings)

## Problem

The self-hosted `.spl` MIR backend (what production `bin/simple` runs) has **no
primitive value-boxing / `any`-tagging primitive at all**. A bare primitive that
flows into an `any`- or optional-typed slot is left raw/untagged, so:

- `val a: any = 9; print a` → `<invalid-heap:0x9>` (not `9`).
- `val mj: i32? = 7; print mj` → `<value:0x7>`; `mj.unwrap_or(9)` / `mj.is_some()`
  → `Function 'is_some' not found`.
- `i32? = 0` / `bool? = false` collide with the nil sentinel.

This is broader than typed optionals — it is the missing `any`-representation
primitive. Fixing it unblocks both `any` values and typed-optional support in the
native/JIT path.

## Goal

Present primitive values carried in `any`/`T?` slots are **tagged/boxed** (BoxInt
= `value<<3 | TAG_INT`, BoxFloat for floats), nil is the tagged sentinel `3`, and
the Option API lowers correctly — so `bin/simple run`/native compile match the
interpreter for `any` and `i32?/f64?/bool?/text?`.

## Scope / work items

1. **MIR boxing primitive (foundational).** Add `BoxInt`/`BoxFloat` + symmetric
   `UnboxInt`/`UnboxFloat` to the `.spl` MIR (lower to `Shl`+`BitOr` / shift, or a
   runtime call). Mirror the Rust seed's `codegen/instr/mod.rs` `BoxInt`
   (`value<<3 | TAG_INT`).
2. **Wire boxing at every coercion site** — `T→any` and `T→T?`: let-binding,
   reassignment, function params, returns, struct-field init, array/dict element.
   (The validated seed prototype only covered `HirStmt::Let` — insufficient.)
3. **Unify the nil sentinel on `3`** (not `0`) so `0`/`false` payloads don't
   collide with nil.
4. **Option-method dispatch** for primitive optionals in
   `src/compiler/50.mir/mir_lowering_expr_part3.spl` `lower_method_call`
   (intercept `Optional(inner)` before `match resolution`, ~L151):
   `is_some`→sentinel `!= 3`, `is_none`→`== 3`, `unwrap`→Unbox (+ nil trap),
   `unwrap_or(x,d)`→`select(is_some, unbox(x), d)`.
5. **`Some()`/`None` constructor form** must produce the same boxed representation
   (currently prints `<enum@0x..>`).
6. **Rust seed parity** (Rust/Simple parity rule): port the same to the seed
   (`hir/lower/expr/mod.rs`, `mir/lower/lowering_stmt.rs`,
   `mir/lower/lowering_expr_builtin.rs`); a non-regressive let-only prototype
   already exists as diffs in workflow run `wf_81e1ad20-5aa` output.

## Acceptance

- `val a: any = 9; print a` → `9`; same for `f64`/`bool`/`text`.
- `i32?/f64?/bool?/text?`: present `print`→value (no `<value:..>`/`<invalid-heap:..>`);
  `unwrap_or`→value-or-default; `is_some`/`is_none` correct; `i32?=0`/`bool?=false`
  are present (NOT nil); `i32?=3` not nil.
- Coercion correct at reassign / param / return / struct-field, not just `let`.
- `Some(x)`/`None` print + unwrap correctly.
- No regression: enums, plain methods, existing test suite, `-c "print(1+1)"`.
- Interpreter and native agree on the full matrix.

## Risk / deploy

- Bootstrap-critical. Requires bootstrap rebuild + `--deploy` (flagged risky in
  `.claude/rules/bootstrap.md`; stage-3 self-host historically flaky). Keep deploy
  human-gated; smoke-test (`bin/simple -c "print(1+1)"` → 2, lint a file) and
  restore-on-break afterward.
- Land seed + `.spl` together (a seed-only change has zero production value —
  `bin/simple` is the self-hosted `.spl` compiler).
