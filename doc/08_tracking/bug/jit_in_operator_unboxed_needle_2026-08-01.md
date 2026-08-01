# `in` returns FALSE for a member that IS present (JIT) — unboxed membership needle

**Date:** 2026-08-01
**Status:** FIXED (all three defects below)
**Severity:** P0 wrong answer — a membership test that silently answers "absent"
skips work in every guard, filter and dedupe built on it.
**Engine:** Cranelift JIT only. The tree-walking interpreter was CORRECT
throughout, which is why no spec caught it: `bin/simple test` hard-defaults to
the interpreter (see `run_vs_test_harness_divergence_2026-07-28.md`).
**Binary under test:** `src/compiler_rust/target/release/simple`, rebuilt from
tip. The pre-fix binary was kept as an explicit control and re-run against the
POST-fix tree, so every delta below is attributable to the code change and not
to source drift.

## Symptom (PROVED)

Under the JIT, `in` answered `false` for a present member whenever the needle
was a raw scalar. Text needles were unaffected — that asymmetry is the
diagnosis.

| probe | expected | JIT before | interpreter before |
|---|---|---|---|
| `2 in [1, 2, 3]` | true | **false** | true |
| `1 in [1, 2, 3]` | true | **false** | true |
| `2.5 in [1.5, 2.5]` | true | **false** | true |
| `true in [true, false]` | true | **false** | true |
| `1 in {1: 10}` | true | **false** | true |
| `0 in [0, 0, 0]` | true | true | true |
| `"world" in "hello world"` | true | true | true |
| `"beta" in ["alpha", "beta"]` | true | true | true |
| `"k1" in {"k1": 10}` | true | true | true |
| `nums.contains(2)` | true | true (see defect 3) | true |
| `if 2 in nums:` | fires | **takes else** | fires |

`0` matched by accident: the zero value is a fixed point of the tag encoding, so
the raw and the tagged form coincide.

`not in` failed differently — branching was right but the VALUE was garbage:

| probe | expected | JIT before |
|---|---|---|
| `("zzz" not in hay).to_text()` | `"true"` | **`"nil"`** |
| `("world" not in hay).to_text()` | `"false"` | **`"0"`** |
| `if "zzz" not in hay:` | fires | fires (correct) |

## Root causes — THREE distinct defects, all in the Rust seed

### 1. The membership needle was passed to `rt_contains` UNBOXED

`src/compiler_rust/compiler/src/codegen/instr/core.rs`, the `BinOp::In |
BinOp::NotIn` arm, called `rt_contains(collection, raw_i64_needle)`.

`rt_contains` (`src/compiler_rust/runtime/src/value/collections.rs:3989`) takes
`RuntimeValue` parameters: for an array it compares each element with
`rt_value_eq`, for a dict it hash-looks-up the key. Both need the needle
*tagged*. A raw `i64` therefore never matched a boxed element.

The `.contains()` / `.has()` / `.contains_key()` path in
`codegen/instr/methods.rs` already boxed it, with a comment saying exactly why —
the operator path simply never got the same treatment. The fix routes `in`
through the same `wrap_value`.

It also uses the **pre-coerce** operands: `coerce_binop_operands` promotes the
other side to float when either side is float, which for `2.5 in floats` would
have converted the collection POINTER to an f64.

### 2. `NotIn` was missing from the HIR BOOL result-type list

`src/compiler_rust/compiler/src/hir/lower/expr/operators.rs:48` listed
`And | Or | Is | In` but not `NotIn`, so a `not in` expression fell through to
`_ => left_hir.ty` and was typed as its LEFT OPERAND (text, for
`"zzz" not in hay`). `.to_text()` then decoded the raw `0`/`1` as a heap handle
and printed `nil`/`0`. Branching still worked, which is why this hid behind
`if x not in y` for so long.

This is the same family as the JIT text-ordering defect fixed in `6469d70eb4e`:
**a value whose static type is not threaded is silently mishandled downstream.**

The `bxor(result, 1)` negation was also replaced with an `icmp`-against-zero,
matching `BinOp::NotEq`: `rt_contains` returns a `u8` whose upper
return-register bits are not guaranteed clear, so xor could leave a value that
is neither 0 nor 1.

### 3. `rt_box_int` / `rt_box_float` DO NOT EXIST in the runtime

`methods.rs` `wrap_value` emitted calls to `rt_box_int` and `rt_box_float`.
Neither symbol is defined anywhere under `src/compiler_rust/runtime` — there is
no `pub extern "C" fn rt_box_int`. The real tagging helpers are `rt_value_int`
and `rt_value_float` (`runtime/src/value/sffi/value_ops.rs:7,11`).

Consequence: any module containing a `.contains(<int>)` hit
`unresolved external symbol 'rt_box_int'` and the JIT **silently dropped the
WHOLE MODULE to the interpreter**, printing
`[jit-fallback] ... whole module dropped to the interpreter (expect ~100-1000x
slowdown)` and **exiting 0**. That is why `nums.contains(2)` looked correct in
the very first probe: that answer came from the interpreter, not the JIT.

This nearly produced a false green for this very fix. The first fixed build
appeared to pass — with the fallback banner in the output. Every verification
below is therefore run under `SIMPLE_JIT_STRICT=1`, which turns the fallback
into a hard error, so a green result is genuinely JIT-executed.

## Fix

- `src/compiler_rust/compiler/src/codegen/instr/core.rs` — box the needle via
  `methods::wrap_value` using the pre-coerce operands; negate `NotIn` with
  `icmp` against zero instead of `bxor`.
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs` — `wrap_value` is
  now `pub(super)`, and emits `rt_value_int` / `rt_value_float` instead of the
  nonexistent `rt_box_int` / `rt_box_float`.
- `src/compiler_rust/compiler/src/hir/lower/expr/operators.rs` — `NotIn` joins
  `In` in the BOOL result-type arm.
- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — `rt_value_int` /
  `rt_value_float` are codegen roots (the `in` arm emits them from a BinOp node,
  which is not a MIR `BuiltinMethod` node), and the stale `rt_box_*` names in
  the `BuiltinMethod` list are corrected.

## Verification

All under `SIMPLE_JIT_STRICT=1` on the rebuilt binary — no fallback banner, so
these are true JIT measurements. Every probe above now answers correctly, and
the true-positive controls that must STAY false still do: `9 in nums`,
`"gamma" in words`, `"zz" in d`, `7 in {1:10}`, `"world" not in hay`,
`9.5 in [1.5, 2.5]`. A fix that merely silenced one engine would have flipped
those too.

Regression spec: `test/01_unit/language/in_operator_membership_spec.spl` —
20 examples, 20 passed. Non-vacuity proved by sabotage: flipping
`assert_true(20 in a)` to `assert_false` gave `20 total, 19 passed, 1 failed`,
exit 1, with the other 19 assertions in the same block staying green; the
sabotage was then reverted.

Focused Rust unit tests (`binop`, `contains`, `box_int`, `box_float`,
`wrap_value`): 99 passed, 0 failed.

`simple test test/01_unit/language` fails identically (`5 total, 0 passed`) on
BOTH the pre-fix control binary and the fixed binary — a pre-existing
directory-run harness problem, not a regression from this change. Individual
spec files run fine.

## Blast radius

**Mechanism-scoped (this is the honest statement of reach):** every `in` /
`not in` in the codebase whose needle is an int, float or bool, on every engine
path that is the Cranelift JIT — which is what a bare `simple <file>.spl` and
`simple run` use. Text needles were never affected, so anything doing substring
or string-set membership was correct all along.

A precise static enumeration of `in` call sites is NOT reliably greppable: `in`
is also the `for ... in` keyword and the most common English preposition, so a
`.spl` sweep for ` in ` returns ~20,000 lines that are overwhelmingly prose in
comments and string literals. The keyword-anchored form (`if`/`while`/`return`/
`and`/`or`/`val =`/`var =` followed by an `X in Y`) finds 13 sites, 2 of them
`not in`, concentrated in `test/03_system` and `test/system` — so **very little
owned code uses the operator form on a scalar needle, and none of it is
load-bearing product code.** Counts taken with `/usr/bin/grep`, excluding
`**/vendor/**`.

Defect 3 has the wider reach, because it is not about answers but about
**performance and engine identity**: `.contains(<numeric literal>)` appears at
601 sites across 115 files (55 under `test/01_unit`, 23 under `test/unit`, 16
under `test/03_system`, 4 under `src/app`). Every one of those modules was
running fully interpreted under the JIT, at the documented 100-1000x penalty,
with exit code 0 and only a stderr banner to say so. Any perf measurement taken
on such a module was measuring the interpreter.

## Not fixed here (filed, adjacent)

- **`x in <range>` diverges between engines.** The JIT now answers `3 in 1..5`
  → true / `9 in 1..5` → false, but the INTERPRETER rejects it outright:
  `semantic: 'in' operator requires array, tuple, dict, or string; got object`.
  One of the two is wrong about whether ranges are a membership receiver at all.
  This is a spec question, not a codegen bug, so it is left for a language
  decision rather than settled unilaterally here.
- **The LLVM backend still emits `rt_box_float`**
  (`codegen/llvm/functions.rs:299`), with a test asserting it in the emitted IR
  (`functions.rs:3596`). Since `rt_box_float` does not exist in the runtime,
  that path is presumed to have the same unresolved-symbol problem the
  Cranelift path had. Out of scope for this change (different backend, its own
  link model), but it is the sibling this fix's family predicts, recorded here
  so it is not lost.
- **`//` at the start of an indented block body lexes as a `Parallel` token**,
  not a comment: `fn main():` followed by an indented `// note` line fails with
  `Unexpected token: expected Indent, found Parallel`. Found incidentally while
  writing the probes; unrelated to `in`.

## Residual risk

`wrap_value` boxes based on `ctx.vreg_types`, i.e. STATIC type information. A
needle whose vreg type was never threaded falls through to the `_ => val`
pass-through and would still be passed raw — the exact fail-open shape that
caused the text-ordering defect in `6469d70eb4e`. It is not reachable from any
probe written here (literals, `val`-bound scalars, and dict keys all carry their
type), but it is the place this defect would come back.
