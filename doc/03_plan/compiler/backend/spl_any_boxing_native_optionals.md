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

## Findings 2026-06-25 (implementation attempt) — design re-scoped

A first implementation attempt (let-site integer boxing) was reverted unbuilt:
the seed-derived model does NOT map to the `.spl` backend. Four findings:

1. **`.spl` optionals are a TUPLE, not a tagged word.** `Type::Optional(inner)`
   lowers to `MirType.Tuple([Bool has_value, inner value])`
   (`src/compiler/50.mir/mir_lowering_part2_part2.spl:272`, "Optional is enum
   {nil, Some(T)}"). So the seed's "box payload `<<3` + nil sentinel `3`" model is
   **wrong for `.spl`** — `<<3` into a tuple slot is corruption. The correct `.spl`
   work is to lower the Option API against the tuple: `is_some`→read `has_value`;
   `is_none`→`!has_value`; `unwrap`→read `value` (+ guard on `has_value`);
   `unwrap_or(d)`→`select(has_value, value, d)`. This is cleaner than the seed and
   has NO nil-sentinel/zero-collision problem. **The optional half is independent
   of the `any`-boxing half.**

2. **The `any`-display bug is a SEPARATE problem from optionals.** `val a: any = 9;
   print a` → `<invalid-heap:0x9>` is about the `any` (type-erased) representation,
   not optionals. And the `any` keyword **never reaches `HirTypeKind.Any`**:
   `lower_type`'s `case Named(...)` (`src/compiler/20.hir/hir_lowering/types.spl`)
   has no `"any"` arm, so `: any` resolves via symbol-lookup default. Adding
   `case "any": HirTypeKind.Any` is a **broad, risky** change — `: any` is used
   pervasively as a function-pointer param/field type (`tokenize_fn`/`parse_fn`/…
   in `src/compiler/00.common/compiler_services.spl`, many backend `*_fn: any`);
   flipping their resolution could break bootstrap. Must be done deliberately with
   a full `: any`-site audit, not as a side effect.

3. **`compile` delegates to the Rust seed.** The full CLI's `compile` subcommand
   shells out to `SIMPLE_BOOTSTRAP_DRIVER` (`cli_sffi.rs:201`, refuses
   self-delegation), so `.spl` MIR edits are NOT exercised via `compile` — only via
   the stage-4 `run` path. Test `.spl` codegen with `<stage4>/simple run`, never
   `compile`.

4. **Self-hosted MIR-emit is stubbed in current builds.** Stage-3 self-host fails
   (pre-existing baseline → "using seed for stage 4"), and the stage-4 log lists
   ~551 stub functions for unresolved symbols **including `builder_emit_const_int`**
   — the self-hosted compiler's own MIR builder path is non-functional, so even a
   correct `.spl` codegen edit can't be exercised end-to-end until self-host is
   repaired or an in-process (non-delegating) compile path exists.

### Revised sequencing
- **(A) Optionals (tuple-based, tractable first):** lower `is_some`/`is_none`/
  `unwrap`/`unwrap_or` against the `{has_value, value}` tuple in
  `src/compiler/50.mir/mir_lowering_expr_part3.spl` `lower_method_call`. No boxing,
  no sentinel. Blocked end-to-end only by (3)/(4) testability.
- **(B) `any` display:** deliberately add the `"any"` → `HirTypeKind.Any` arm +
  audit every `: any` fn-pointer site; then box primitive payloads entering `any`.
  Independent of (A).
- **(C) Infra prerequisite:** fix stage-3 self-host stubs (esp. `builder_emit_*`)
  or provide an in-process `compile`, so `.spl` codegen is testable without the
  seed. (A)/(B) cannot be verified end-to-end until this lands.
