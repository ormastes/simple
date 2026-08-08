# Seed JIT silently accepts an unknown field name in named-argument construction

**Status:** FIXED (seed) / OPEN (pure-Simple, unverifiable — see Follow-up)
**Found:** 2026-08-08, while building the positive control for
`interp_static_fn_new_hijacks_named_ctor_2026-07-02` (which was briefly closed
RESOLVED and has since been REOPENED as partially fixed; this is still a
distinct defect)
**Severity:** medium — a typo'd field name compiles and runs with no diagnostic,
and the value lands in the wrong slot rather than being rejected
**Engine:** seed JIT only. The interpreter is correct **for this class of name
only** — see the caveat below; it is not a safe reference lane in general.

> **Caveat (added 2026-08-08 by adversarial re-review).** "Interpreter is
> CORRECT" holds only for a name matching NEITHER a field NOR a parameter of a
> `static fn new`. The interpreter attempts `new`-dispatch BEFORE it validates
> against the field list, so `Font(path: "x", size: 8)` — where `path` is a
> parameter of `new` and not a field — is silently routed to `static fn new`
> instead of being rejected. That is the still-open hijack tracked in
> `interp_static_fn_new_hijacks_named_ctor_2026-07-02.md` (REOPENED). Do not
> treat the interpreter as an oracle for named-argument validation.

## Symptom

```simple
class Widget:
    id: i64
    size: i64
    static fn new(path: text, size: i64) -> Widget:
        Widget(id: 0, size: size)

fn main():
    val w = Widget(bogus: 3, size: 4)
    print "id={w.id} size={w.size}"
main()
```

| lane | command | result |
|------|---------|--------|
| interpreter | `SIMPLE_EXECUTION_MODE=interpreter bin/simple run r.spl` | `error: semantic: class `Widget` has no field named `bogus`` — CORRECT |
| seed JIT | `bin/simple run r.spl` (default) | `id=3 size=4` — WRONG, no diagnostic |

`bogus` is not a field of `Widget`. The interpreter rejects it. The JIT accepts
it silently.

## What the JIT actually does (characterised 2026-08-08, seed JIT)

An earlier draft of this report guessed "the arguments bind positionally". That
guess is WRONG, and the discriminator is a reversed-order call:

| call | JIT result | reading |
|------|-----------|---------|
| `Widget(id: 3, size: 4)` | `id=3 size=4` | correct |
| `Widget(size: 4, id: 3)` | `id=3 size=4` | **names ARE honoured** — a positional binder would have given `id=4 size=3` |
| `Widget(bogus: 3, size: 4)` | `id=3 size=4` | unknown name silently accepted; its value lands in the leftover field `id` |
| `Widget(size: 4, bogus: 3)` | `id=3 size=4` | same, order-independent |
| `Widget(id: 3, bogus: 4)` | `id=3 size=3` | unknown name accepted and `size` gets **3** — neither the supplied `4` nor a default |

So the defect is narrower but stranger than "positional": known field names bind
correctly by name in any order, and an **unknown** name is neither rejected nor
dropped — it is silently absorbed into whichever field slot is still unfilled,
and in the last row it corrupts that slot with an unrelated value (`3`, the
value of the preceding argument) rather than the one written (`4`).

That last row is the sharp edge: a single mistyped field name produces a
constructed object in which a *correctly spelled* field also holds the wrong
value, with no diagnostic on any line.

## Why this matters

Named-argument construction (`Point(x: 3, y: 4)`) is the house-style
constructor form per `.claude/rules/language.md`, so this is the common path.
A misspelled or renamed field is silently ignored on the engine that ordinary
programs run on (`bin/simple run` = JIT), while `bin/simple test` runs the
interpreter and would catch it — a classic run/test divergence of the family
already catalogued in `run_vs_test_harness_divergence_2026-07-28.md`.

And per the table above the failure is silent-*wrong*, not merely permissive:
`Widget(id: 3, bogus: 4)` yields `size=3`, so one typo corrupts a field the
author spelled correctly.

## Not fixed here

The named-argument binder for the JIT lane lives in the Rust seed
(`src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs` is the
interpreter side that gets this right; the JIT lowering path does not consult
it). Rust is bootstrap-only per repo rules, so the fix belongs in the
pure-Simple lowering lane, or in a front-end check that runs before lowering so
both engines inherit it. Recorded rather than guessed.

## Binary identity

`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which prints the
"Rust-built Simple binary is a bootstrap seed only" banner. No pure-Simple
self-hosted binary is deployed on this host, so the self-hosted lane is
untested — the divergence above is seed-JIT vs seed-interpreter.

## Correction 2026-08-08 (adversarial re-review) — the mechanism above is WRONG

The table's reading — "the unknown name is silently absorbed into whichever
field slot is still unfilled ... it corrupts that slot with an unrelated value
(`3`, the value of the preceding argument)" — is not what happens. It was
inferred from probes in which the literal `3` happened to be present.

Vary the values and `3` does not move:

    class Font:
        id: i64
        size: i64
        static fn new(path: text, size: i64) -> Font:
            Font(id: 77, size: size)

    Font(bogus: 111, size: 8)   seed JIT -> id=3 size=8
    Font(bogus: 222, size: 9)   seed JIT -> id=3 size=9
    Font(id: 5, bogus: 999)     seed JIT -> id=5 size=3

The leftover slot is filled with the **constant 3** regardless of the supplied
argument (`111`, `222`, `999` all vanish). The unknown argument's value is not
absorbed anywhere; it is dropped, and the unfilled field is initialised from
garbage that happens to read as `3` on this build. Treat `3` as an artifact, not
as a rule.

Two further scope corrections:

- **It is not conditioned on `static fn new`.** The same class with no static at
  all reproduces identically:

        class Plain:
            id: i64
            size: i64

        Plain(bogus: 111, size: 8)  seed JIT -> id=3 size=8   (interpreter: error)
        Plain(id: 5, bogus: 999)    seed JIT -> id=5 size=3

  So this is a plain named-argument-validation hole in the JIT lowering, not
  anything to do with static-constructor dispatch.
- **Severity is understated at "medium".** The sibling report
  `interp_static_fn_new_hijacks_named_ctor_2026-07-02` rates the same class of
  failure — silent wrong-field construction on the default `run` engine — at P1.
  A typo'd field name yields an object with a garbage value in a field the
  author never named, with no diagnostic on any line, on the engine ordinary
  programs use. Read this as **high**.

The core symptom in the report body (interpreter rejects the unknown name, seed
JIT silently accepts it) is confirmed and unchanged.


---

## RESOLVED (seed) — 2026-08-08

### Root cause

`src/compiler_rust/compiler/src/hir/lower/expr/collections.rs`,
`lower_struct_init_fields` (the single choke point both AST shapes route
through: the paren-call ctor `S(f: v)` via `hir/lower/expr/calls.rs:109`, and
the brace literal `S { f: v }` via `lower_struct_init`, collections.rs:213).

It built a `named: HashMap<&str, &Expr>` from the call's named arguments, then
walked the struct's DECLARED field list, taking `named[field]` for each field it
recognised. **An argument whose name matched no declared field was inserted into
that map, never consumed by the loop, and never validated.** The declared slot
the author meant to fill therefore stayed unfilled and fell through to the
loop's `HirExprKind::Nil` placeholder.

### The constant `3` IS a leaked tag — confirmed

`HirExprKind::Nil` lowers via `lower_nil_expr`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_literal.rs:44-53`),
whose own comment states it: *"Nil is tagged value 3 in the runtime
(TAG_SPECIAL=0b011 | SPECIAL_NIL=0)"* — it emits `MirInst::ConstInt { value: 3 }`.
Read back through an `i64`-typed field, that tag surfaces **untagged** as the
literal integer 3. So the corrupt slot holds a **leaked discriminant**, not a
value.

This also **disproves** this report's original "the value of the preceding
argument" reading. A three-field class settles it:

| call | observed |
|------|----------|
| `T3(b: 7, zzz: 99)` | `a=3 b=7 c=3` |

Two *independent* unfilled slots both hold 3. No "value shifted into the
neighbouring slot" explanation can produce that. The tag is also not conditioned
on a `static fn new` — `class Font { id, size }` with no statics reproduces it.

### Fix

Reject a named argument matching no declared field, as
`LowerError::CannotInferFieldType` — which already renders as
``class `X` has no field named `Y` `` with a did-you-mean suggestion, matching
the interpreter's wording exactly.

### Soundness gate (why the rejection is scoped to same-file declarations)

Rejecting on the resolved field list **alone** false-positives badly. Measured
over 400 repo `.spl` files: **21 hits, and every one inspected was a bare-name
collision, not a typo.** The tell is that the same sweep reported BOTH
``Span`` field `end` AND ``Span`` field `end_pos`, which is only possible with
two different `Span` structs — `src/compiler/00.common/diagnostics/span.spl` has
`end`, `src/compiler/10.frontend/core/lexer_types.spl` has `end_pos`. Same for
`Rect.x`, `CompileOptions.mode`, `Diagnostic.range`.

Cause: ~1,522 class/struct bare names are duplicated across
`src/{compiler,lib,app}`, and `TypeRegistry::name_to_id` is **bare-keyed,
last-registration-wins**. For an IMPORTED name the resolved layout may not be
the one the author meant, so "not in the declared list" would only mean "the
registry picked the wrong struct" — the separate collision family fixed for MIR
field *reads* in `b9e23914a0e`. Neither `global_struct_defs` nor
`duplicate_global_struct_defs` can rescue it: both are populated only by the
native_project driver and are **None under `simple run`** (verified — adding
them changed the hit count 21 → 21), and the losing declaration is absent from
the registry entirely, so the collision is not observable from HIR at all.

So the rejection fires only when the struct/class is **declared in the same file
as the construction site**, tracked by a new `Lowerer::struct_decl_files`
recorded in `register_class` / `register_struct`
(`hir/lower/type_registration.rs`). Same-file declarations have no ambiguity.
Result: **21 -> 2 false positives across the same 400-file sweep** (both
residual hits are ``Rect`` field `x`), with both repro classes still rejected.

**Correction (same day):** an earlier revision of this section claimed *0* false
positives. That was wrong -- it was written from a partial sweep before the run
finished. The measured figure is **2 of 400 (0.5%)**, down from 21.

The 2 residual hits are the same collision family, one step further in: a file
declares `Rect` locally AND constructs it, but a LATER import re-registers the
bare name and wins `name_to_id`, so `struct_ty` resolves to a foreign `Rect`
while the same-file test still passes.

A tightening was attempted and **rejected**: key `struct_decl_files` by
`(declaring file, name)` and additionally require the resolved field list to
equal the locally-declared one. It made the sweep **worse (4+ hits, including
two `Span` cases the current gate suppresses)**, because `Lowerer::current_file`
does not vary the way that fix assumes -- imports are lowered without it being
re-pointed, so every declaration lands under the same key and the extra
condition is vacuous. The change was reverted, not landed. Closing the residual
2 therefore needs a real module-qualified HIR type tier (the analogue of
`b9e23914a0e` for MIR field reads), not another heuristic on `current_file`.

**Remaining gap:** a typo'd field name on an **imported** struct is still
silently accepted. Closing it requires a module-qualified tier for HIR type
resolution — the analogue of what `b9e23914a0e` added for MIR field reads.

### Family enumeration

| form | before | after | same root cause? |
|------|--------|-------|------------------|
| ctor named arg, unknown name (same-file class) | silent, slot = tag 3 | **compile error** | yes — fixed |
| ctor named arg, unknown name (imported class) | silent, slot = tag 3 | still silent | yes — blocked on bare-name collision |
| brace literal `S { bogus: v }` | silent | **compile error** | yes — same choke point, fixed |
| duplicate named arg `W(size: 1, size: 2)` | silent; last wins, other slot = tag 3 (`id=3 size=2`) | unchanged | same choke point (`named.insert` drops the earlier) — **NOT fixed, needs its own report** |
| `static fn new` param name, e.g. `W(path: "x", size: 8)` where `path` is a `new` param and not a field | JIT **bypassed `new` entirely** and built a StructInit → `id=3` | JIT falls back to the interpreter, which routes to `new` → `id=42` (**correct**) | yes — incidentally corrected |
| **free fn / method named arg**, `f(a: 1, zzz: 2)` | silent: `zzz` bound positionally to `b`, result 102, rc=0 | **unchanged — still silent** | **NO** — different path (`lower_call_args`, which drops names entirely); no tag corruption, it binds positionally. Interpreter rejects it (`unknown argument 'zzz'`). Needs its own report. |

### Verification

`scripts/check/check-named-ctor-unknown-field-rejected.shs` — a shell guard, not
a spec: `bin/simple test` is the INTERPRETER, which already rejected these names
correctly before the fix, so a spec goes red for the wrong reason and proves
nothing. Asserts control flow and exact values, under the default engine and
`SIMPLE_EXECUTION_MODE=jit`.

Both directions proven against real binaries:

* **RED** (unfixed deployed seed `bin/simple`): `FAIL — red1 [default]: exit 0
  — an unknown field name was ACCEPTED`, output `MARKER id=3 size=8`, rc=1.
* **GREEN** (patched seed): `PASS — 8 checks`, rc=0.

## Follow-up: pure-Simple shares the defect (OPEN)

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3038`,
`lower_struct_construct` — the single construction mapper for both `S(f: v)` and
`S { f: v }` (dispatch at :4109). `named_args` occurs at exactly 4 sites (3062
insert-decl, 3074 insert, 3110 `has`, 3191 read); there is **no** reconciliation
of leftover keys and no unknown-name diagnostic. Its unfilled-slot fill is
`ensure_option_handle(const_int(3))` for Optional fields — **the same NIL tag
3** — else `Const(Int(0))`. Its interpreter has the diagnostic
(`10.frontend/core/interpreter/eval_calls.spl:458`, "unknown field '...' in ...
constructor"), so it has the identical compile-vs-interpret divergence.

Deliberately **not** patched here, for two blocking reasons:

1. **Unverifiable right now.** Stage-3 self-host is blocked
   (`.claude/rules/bootstrap.md`; `bin/simple` is the Rust seed), so a
   pure-Simple compiler edit cannot be built or run, and an unmeasured
   hard-error in a hot lowering function is exactly how legitimate code gets
   redded.
2. **Its field map is bare-keyed too, and worse.** `struct_field_order` is
   keyed by bare class name over the same ~1,522 duplicated names — that map IS
   the subject of `b9e23914a0e`, which added a module-qualified tier for
   `resolve_field_index` (field READS) only. The same-file gate used for the
   seed needs that qualified tier extended to construction before it can be
   applied here, and the blast radius cannot be measured without a buildable
   compiler.
