# JIT text ordering (`<` `<=` `>` `>=`) compared POINTERS, not content

**Date:** 2026-08-01
**Severity:** P0 (silent wrong answers, no diagnostic, engine-divergent)
**Status:** Fixed
**Engines affected:** Cranelift **JIT** (and the shared cranelift codegen arm).
The tree-walking interpreter was always CORRECT.
**Related:** `doc/08_tracking/bug/sspec_test_path_false_green_undercount_2026-07-20.md`
(the 2026-07-22 partial fix this bug completes)

## Summary

Text ordering comparisons under the JIT compared the operands' **heap handle
addresses** instead of their **byte content**, whenever codegen could not
*statically* prove that **both** operands were `TypeId::STRING`.

Equality (`==` / `!=`) was **not** affected. That asymmetry is what made the
defect so hard to name: at the lint level the observable behaviour looked like
"`>=` is evaluating as `==`", when the real mechanism was address ordering.

## How it surfaced

A sibling lane routed `simple lint` through the JIT instead of the interpreter
(13/13 tests pass, **11.9x faster**) and held the change back because lint
output changed: the JIT invented `MODINIT001` false positives.

The rule at `src/compiler/35.semantics/lint/module_init_literal.spl:150` is a
plain ASCII digit-range check:

    val is_digit = ch >= "0" and ch <= "9"

`ch` comes from `s.substring(i, i + 1)`. Under the JIT this returned `false`
for most digits, so `_mil_is_numeric_literal` rejected numeric initializers and
`var d1 = 7` was flagged as a non-literal module initializer.

`= 0` happened to lint clean and `= 7` did not, purely by where the literals
landed in the string pool — which is exactly the signature of address ordering.
**The lint rule is correct; the engine was wrong.**

## Reproducer (operator level, not through lint)

    fn probe(t: text) -> void:
        val ch = t.substring(0, 1)
        print("${t} ge0=${ch >= "0"} le9=${ch <= "9"}")

Measured with the same binary, one process per run:

| input | interpreter (`SIMPLE_EXECUTION_MODE=interpret`) | JIT (`SIMPLE_EXECUTION_MODE=jit`) |
|---|---|---|
| `"0"` | `ge0=T le9=T` (correct)  | `ge0=T le9=F` **WRONG** |
| `"7"` | `ge0=T le9=T` (correct)  | `ge0=F le9=F` **WRONG** |
| `"9"` | `ge0=T le9=T` (correct)  | `ge0=F le9=T` **WRONG** |
| `"a"` | `ge0=T le9=F` (correct)  | `ge0=T le9=F` (right by accident) |
| `"/"` | `ge0=F le9=T` (correct)  | `ge0=T le9=F` **WRONG** |

Literal-vs-literal comparisons (`"7" >= "0"`) were correct on **both** engines —
only a **runtime-produced** operand triggered it.

**Shape sensitivity — important when writing a regression guard.** Because the
guard depended on whatever static type info happened to survive to codegen, the
defect did not fire for every substring. A substring of a bare *literal* often
kept its typing and answered correctly even before the fix; the receiver
arriving as a **function parameter** is what reliably lost it. Two shapes
measured wrong under the pre-fix JIT and right under the interpreter:

    fn ge_zero(t: text) -> bool:
        val ch = t.substring(0, 1)
        ch >= "0"
    # ge_zero("/")  -> interpreter: false (correct, '/' is 0x2F < '0' 0x30)
    #               -> pre-fix JIT: TRUE   (wrong)

    fn lower_lt(a: text, b: text) -> bool:
        a.lower() < b.lower()
    # lower_lt("apple","banana") -> both engines: true
    # lower_lt("banana","apple") -> interpreter: false (correct)
    #                            -> pre-fix JIT: TRUE  (wrong)

The second is the more alarming one: the comparator was not even
**antisymmetric**, so any text sort built on it silently corrupted its ordering.

Note the mode value is `interpret`, not `interp`; an unrecognised value silently
falls back to the JIT, which will make the two columns look identical.

## Root cause

`src/compiler_rust/compiler/src/codegen/instr/core.rs`, the
`BinOp::Lt | Gt | LtEq | GtEq` arm. The 2026-07-22 P0 fix added a text fast path
guarded by:

    } else if vreg_is_text(ctx, left_vreg) && vreg_is_text(ctx, right_vreg) {
        // rt_text_cmp_any -- correct content compare

`vreg_is_text` is purely static: `ctx.vreg_types.get(&v) == Some(TypeId::STRING)`.
A `.substring()` result does not get its vreg type threaded, so the `&&` guard
failed and the comparison fell through to the **final else** — the raw integer
`icmp` arm — comparing tagged heap-string handles as opaque integers.

So the 2026-07-22 fix removed address ordering only for the statically typed
case and left it live for the untyped case.

`Eq` / `NotEq` did not have this hole because their final else is **not** a raw
`icmp`: it is `rt_native_eq` / `rt_native_neq`, a tag-aware dynamic dispatch
that content-compares tagged heap strings. Ordering had no such counterpart.

## Fix

1. **Relax the static guard from `&&` to `||`.** Simple is statically typed, so
   one side being known text proves the comparison is a text comparison;
   `rt_text_cmp_any` already normalizes tagged-or-raw on both sides.
2. **Add `rt_native_cmp`, the ordering counterpart of `rt_native_eq`**, and use
   it when *neither* operand is statically typed. Tag-aware: content-compares
   tagged heap strings, otherwise raw signed integer compare.
3. Gate (2) on the operands **not** being statically known scalars, so genuine
   integer comparisons keep the inline `icmp` and take **no** runtime-call cost.

Files:
- `src/compiler_rust/compiler/src/codegen/instr/core.rs` — guard + new arm
- `src/compiler_rust/runtime/src/value/sffi/equality.rs` — `rt_native_cmp`
  (Rust runtime; **this is the one the JIT links**)
- `src/runtime/runtime_native.c`, `src/runtime/runtime.h` — C-runtime
  `rt_native_cmp` for the native/AOT path
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — signature spec
- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — codegen root
  (emitted directly from a BinOp node, never as a MIR call node, so without
  this `call_runtime_2` panics with "missing runtime fn")
- `src/compiler_rust/common/src/runtime_symbols.rs` — symbol lists + tier
- `src/compiler_rust/compiler/src/codegen/instr/body.rs` — return type

## Regression guard

`test/01_unit/bugs/text_ordering_cmp_spec.spl` — a new
`describe "text ordering is content-based for runtime-produced (untyped)
operands"` block with 6 examples covering: substring-vs-literal in/below/above
the digit range, the lint rule's exact shape, and substring-vs-substring (the
case that needs the dynamic `rt_native_cmp` fallback rather than the static
`rt_text_cmp_any` arm). The pre-existing literal-operand block is retained
unchanged and acts as the control.

## Blast radius

Any Simple code doing **ordering** comparison on text where at least one operand
is runtime-produced was silently wrong under the JIT. Enumerated families:

- **ASCII / char-class range checks** — dominant family, ~1,150 sites in `src/**`
  (`ch >= "0" and ch <= "9"`, `>= "a"`, `<= "Z"`, ...). Includes
  `src/lib/common/json/parser.spl:114,117,122,131` and
  `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:148,159`.
- **Lexicographic sorting** — `src/app/office/database/qbe.spl:84`,
  `src/app/office/database/query.spl:44`,
  `src/app/llm_caret/claude_full/components/LogSelector.spl:564`,
  `src/compiler_rust/lib/std/src/core/string_traits.spl:39,41`.
- **Version comparison** — `semver_old.spl` prerelease ordering (3 sites across
  the sync/async/gc tiers).
- **Lint rules reachable from `simple lint`** — 21 confirmed-impact sites under
  `src/compiler/35.semantics/lint/` (18) and `src/compiler/90.tools/lint/` (3),
  plus ~24 more in the lexer/parser/common code every lint run touches.

Sites were only *wrong* when they actually ran under the JIT with an untyped
operand; interpreter runs were correct throughout, which is why the whole
family stayed invisible.

## Lessons

- **A guard that needs static type info is a fail-OPEN guard.** The 2026-07-22
  fix was correct but its `&&` precondition silently reverted to the buggy
  behaviour whenever inference was incomplete. When a correctness fix is
  conditional on an analysis, the fallback must also be correct — not the
  original defect.
- **Check the sibling operator.** `Eq` had the right shape (static fast path +
  dynamic tag-aware fallback) the whole time. The ordering arm was missing only
  the second half.
- `SIMPLE_EXECUTION_MODE` takes `interpret` **or** `interpreter` — both are
  accepted (`src/compiler_rust/driver/src/exec_core.rs:38`,
  `"interpret" | "interpreter" => ExecutionMode::Interpret`). `interp` is NOT.
  An unrecognised value falls back to the JIT **silently**
  (`exec_core.rs:74-76`, `.unwrap_or(ExecutionMode::Jit)`), which makes an A/B
  look like agreement. Cheapest self-check: if your two columns ever *disagree*
  on any row, they genuinely ran different engines.

## `to_text()` does NOT lie — the sibling bug report is FALSIFIED

`case_bare_ident_is_irrefutable_binding_2026-08-01.md` recorded a second,
scarier defect alongside this one: that `.to_text()` on the resulting bool
"printed `false` for a comparison that is true", i.e. *a debug print here lies*.
That would be far worse than the miscompile, because it would invalidate any
evidence gathered by printing a bool.

**It is not true.** Re-measured 2026-08-01 with a probe that prints a **branch
side-effect** (distinct strings emitted from the `if` and the `else` arm)
*alongside* `.to_text()` on the same value, across both engines, with a
deliberately-failing sentinel row to prove the probe could report failure at all.

`branch=` and `to_text=` **agreed on every row of every run — including every
wrong row.** `to_text` faithfully reported `false`; the comparison had genuinely
computed `false`. There is one bug here, not two.

The original report reached the opposite conclusion by reasoning "the comparison
is obviously true, therefore the printer must be lying" — correct semantics,
wrong suspect. This is distinct from the known `to_text`-on-erased-`Any`-bool
corruption (`reference_to_text_on_erased_any_bool_corrupt`), which is a real and
still-open defect but does not apply to this shape.

**Method note worth keeping:** "the output lies" and "the computation is wrong"
produce identical printed evidence and demand completely different responses.
Only a branch side-effect distinguishes them. Never let a printed bool be the
sole signal when the bool itself is what is under suspicion.
