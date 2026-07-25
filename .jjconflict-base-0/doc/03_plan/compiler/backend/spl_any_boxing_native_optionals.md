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
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` `lower_method_call`
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
   (`src/compiler/50.mir/_MirLowering/function_lowering.spl:272`, "Optional is enum
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
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` `lower_method_call`. No boxing,
  no sentinel. Blocked end-to-end only by (3)/(4) testability.
- **(B) `any` display:** deliberately add the `"any"` → `HirTypeKind.Any` arm +
  audit every `: any` fn-pointer site; then box primitive payloads entering `any`.
  Independent of (A).
- **(C) Infra prerequisite:** fix stage-3 self-host stubs (esp. `builder_emit_*`)
  or provide an in-process `compile`, so `.spl` codegen is testable without the
  seed. (A)/(B) cannot be verified end-to-end until this lands.
## (C) testability diagnosis 2026-06-25 — gated by deep self-host failure

Attempting (C) "make `.spl` codegen testable" revealed it is gated by the
long-standing self-host failure (see `project_bootstrap_stage3_selfhost_broken`),
not a small enabler:

- **stage-2 is a stub.** `bootstrap_main.spl` `compile` only prints
  `"compile: <file>"` (no codegen); `native-build` errors "rebuild with the full
  Simple driver." So stage-2 cannot test `.spl` codegen.
- **full-CLI build completes but stubs 551 unresolved symbols.** The seed→full
  build (`build/bootstrap/full/.../simple`, 782 compiled/0 failed) emits
  "Generating 551 stub functions for unresolved symbols." Categories (systematic,
  not 551 independent bugs): `*__ParserModule` per-module singletons (dominant),
  `builder_emit_*` SPIR-V builders, `BidirHirExpr_dot_*` method dispatch, `Jit*`
  (JitMapper/JitInstantiator), builtins (`Dict`/`alloc`/`chars_len`), and libc
  externs (`cfgetispeed@GLIBC`). The compiler's own backend codegen + parser
  modules are stubbed in the self-hosted binary → native codegen is unreachable.
- **fresh full-CLI `run` is non-functional.** `<full>/simple run p11.spl`
  (`print(1+1)`) exits rc=0 with NO output. Only the STALE deployed `bin/simple`
  runs (via interpreter fallback), and it predates current sources.

**Consequence:** A/B (native optional/`any` codegen) cannot be verified
end-to-end until self-host produces a binary whose native codegen actually links
and runs. (C) is therefore the foundational blocker — a dedicated self-host
repair project.

**Highest-leverage entry point:** the `*__ParserModule` systematic emission/
resolution gap (one unresolved singleton per module) likely accounts for the
largest share; resolving how module `ParserModule` singletons are emitted/named
in the self-hosted backend is the first sub-problem to attack. Then `builder_emit_*`
(SPIR-V builder module not linked) and `BidirHirExpr_dot_*` (method-symbol
mangling). Diagnose against `build/bootstrap/logs/.../stage4-native-build.log`.

## CORRECTION 2026-06-25 — (C) was a STALE-build mirage; real gap is localized

The "551-symbol self-host rewrite" framing above is **wrong** — it measured a
stale/separate build. The self-hosted `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, rebuilt 2026-06-25 11:09 by a
parallel session) **runs `.spl` codegen correctly**:

- `run print(1+1)` → `2`; `val a: i32 = 7` → `7`; inferred `val e = 7` → `7`.

So (C) "make `.spl` codegen testable" is **already satisfied** — production
`bin/simple run` *is* the harness. No self-host repair is needed. Do not chase
the 551 symbols.

**The real, directly-reproducible bug (production `bin/simple run`):**
primitive payloads entering `any`/`T?` are stored **raw (untagged)**:

- `val a: any = 9` → `<invalid-heap:0x9>` (raw 9; 9&7=1=TAG_HEAP misread)
- `val b: i32? = 7` → `b={<value:0x7>}` (raw 7; 7&7=7=TAG_SPECIAL misread),
  `b.unwrap_or(9)` → `nil`, `match b { Some(x) }` → `x=nil`. nil case
  `c.unwrap_or(5)` → `nil`. (`b.?`/is_some ARE correct — they only test nil-vs-not.)
- Heap-typed optionals (`text?`, struct?) already work — a heap pointer is a
  valid tagged word. Only **primitives** (i32/i64/bool/f64) break.

**Root cause — the in-tree boxing edit is DEAD.** `mir_lowering_stmts.spl:44-79`
intends `value << 3` boxing for ints entering Any/Optional, but the raw
(un-shifted) values above prove the `Shl` never executes — the gate
(`type_.?` + IntLit/Int arm) doesn't match at the `Let`. Worse, the design is
**incoherent**: `_MirLowering/function_lowering.spl:271` declares `Optional → Tuple([Bool
has_value, inner value])`, but the de-facto runtime repr is **bare-payload single
word** (present=value, absent=nil), and there is **no unboxing** at any consumer
(print / unwrap_or / unwrap / match Some). Two conflicting representations, both
half-built.

**REPRESENTATION DECISION REQUIRED before coding** (the implementations diverge):
1. **Boxed tagged value** (mirrors the seed interpreter bare-payload fix): box
   primitives (`<<3`) on entry to any/`T?`; the boxed word is a valid tagged
   value so `print` already renders it; unbox (`>>3`) only when materializing a
   concrete primitive (unwrap/match binding/arithmetic). Smallest diff; boxed-0
   (=0, TAG_INT) is distinct from nil (TAG_SPECIAL=3) so the old 0/nil collision
   dissolves. Cost: unbox sites must be found.
2. **Real tuple `{has_value, value}`** (what `lower_type` already declares):
   construct the tuple at `Let`, extract `.1` at consumers. No tag games. Cost:
   wire tuple construct/extract through unwrap_or/match/print; delete the boxing
   branch.

**Recommendation: (1) boxed tagged value** — it matches what the runtime already
does for `any`, makes `print` work for free, and is the shorter diff; the tuple
form duplicates machinery the tagged-value model already has. Either way, fix the
dead gate first. Iteration cost ≈134s self-host rebuild per change (tractable).

## CORRECTION-of-CORRECTION 2026-06-25 — prior "runs fine" measured the SEED, not self-host

The section above ("(C) was a STALE-build mirage; `.spl` codegen runs") is itself
**wrong**: it tested `bin/simple`, which is a **~30 MB Rust seed** build
(`bin/release/.../simple`, 30,335,240 B, md5 053e2f4) — NOT the self-hosted
compiler. The self-hosted binary is the **17 MB** `build/bootstrap/full/.../simple`
(`full_bin`, 17,327,408 B). They are different programs; `result=2`/`unwrap_or=nil`
came from the seed's interpreter, not `.spl` codegen.

Verified against a fresh `--pure-simple` build (stage4: 782 compiled / 0 failed,
141 s) of `full_bin`:
- `full_bin run <file>` → exits rc=0 doing nothing (a compile-time `eprint` added
  to the `Let` MIR lowering never fired — `run` does not reach lowering/execution).
- `full_bin -c 'print(1+1)'` → **rc=248**, empty stdout (×3). Caveat: the host was
  at **load ~14** (continuous parallel bootstrap builds rewriting `full_bin`), so
  "crashed" vs "starved" is not cleanly separable here.

**Net blocker for A/B (and for verifying ANY `.spl` codegen change):** there is no
usable self-hosted execution path in this environment. The only runnable `simple`
is the seed; `full_bin`'s `run`/`-c` are broken-or-unverifiable; `--deploy` (the
route to a delegate-backed working binary at `bin/simple`) is **human-gated**; and
parallel sessions continuously rewrite `full_bin` + saturate the machine, so
controlled iterative testing is not feasible. Implementing optional/`any`
value-semantics blind (no run-time verification) would violate "leave a runnable
check." **Needs a human to either deploy a known-good `full_bin` or quiet the box
so `full_bin -c`/`run` can be trusted, before the feature build is testable.**
