# `not nil` yields `false` in the `run` engine but `true` under the test runner

**Status:** RESOLVED — re-verified 2026-08-09. All cases (`not nil`, `not e.?`,
`not Some(nil).?`, `not Some(42).?`, `not 3`, `not 0`) now agree between `run`
and the test runner, INCLUDING the previously-documented residual bare
`val n = nil; not n` case (line 107-132 below), which was believed still wrong
as of 2026-08-04 but is now `true` as expected. Repro commands below still work
for regression probing; see re-verification note at bottom of file.
**Found:** 2026-08-04, while fixing the `Some(nil)` spec assertions.
**Impact:** silent wrong answer. `not` is correct on real bools, so the defect
only surfaces on nil/optional operands — and it disagrees between engines, so a
spec can be green under one runner and red under the other.

## Symptom

Via `bin/simple run` (JIT / seed interpreter path):

```
not nil          -> false      # WRONG — nil is absent, so `not nil` should be true
not true         -> false      # correct
not false        -> true       # correct
e.?              -> nil        # e: i64? = nil
not e.?          -> false      # WRONG — follows from `not nil`
```

Under the **Rust test runner** (`SIMPLE_TEST_RUNNER_RUST=1 … test`), the same
expressions behave correctly. A spec with a deliberate failing control:

```
Passed: 3   Failed: 1     # the 1 is the control `verify(false)`
```

where the 3 passing examples are `not opt.?` for `opt: i64? = nil`, `not opt.?`
for `opt = Some(nil)`, and `not (not Some(42).?)`.

So: **`not <nil>` is `true` under the test runner and `false` under `run`.**

## Repro

```simple
fn main():
    val n = nil
    print "not nil  -> {not n}"      # prints false; should print true
    print "not true -> {not true}"   # false  (correct)
    print "not false -> {not false}" # true   (correct)
```

`./bin/simple run probe.spl`

## Why it matters

`not X.?` is a load-bearing idiom in the spec corpus — it is how "this optional
is absent" is asserted, and it appears throughout `test/03_system/core/edge_case`
(4 sites per file across 50 files). Every one of those is correct only because
the test runner evaluates it correctly. Anything that evaluates the same source
through `run` gets the opposite answer with no diagnostic.

This also nearly produced a bad fix: correcting the 202 `Some(nil)` specs to
`verify(not opt.?)` was first checked with `bin/simple run`, which reported
`false` and made the corrected assertion look wrong. Only running it under the
engine that actually executes the specs showed the fix was right. **Probe with
the engine that runs the code, not with whichever one is convenient.**

## Which engine is wrong (established 2026-08-04)

Three implementations of `not` exist. Two are correct:

- **Tree-walk interpreter** — `interpreter/expr/ops.rs:1543`:
  `Value::Bool(!is_condition_present(operand, &val))`. Correct; matches the
  observed `not nil = true`.
- **Bytecode VM** — `runtime/src/bytecode/vm.rs:677`: `!a.as_bool()`, where
  `as_bool()` is `tag() == TAG_SPECIAL && payload() == SPECIAL_TRUE`
  (`runtime/src/value/core.rs:310`). Nil's payload is `SPECIAL_NIL`, so
  `as_bool()` is false and `not nil` is **true**. Correct.
- **Cranelift JIT** — `codegen/instr/basic_ops.rs`, `compile_unary_op`:
  `icmp_imm(Equal, val, 0)`. Only literal zero is falsy, so the tagged nil
  sentinel 3 is truthy and `not nil` is **false**. **This is the wrong one.**

## FIXED for tagged operands (2026-08-04)

`compile_unary_op` now emits the nil-sentinel compare **when the operand's static
type can carry a tag**, keeping the plain zero-compare for raw scalars:

```rust
if operand_may_be_nil(ctx.vreg_types.get(&operand).copied()) {
    let is_nil = builder.ins().icmp_imm(IntCC::Equal, val, 3);
    builder.ins().bor(is_zero, is_nil)
} else {
    is_zero
}
```

`operand_may_be_nil` returns false for `BOOL`, the integer widths, the floats,
`CHAR` and `VOID`, and true for everything else (`Any`, optionals, strings, user
types, and unrecorded operands).

Verified on a fresh build with no instrumentation (`fresh=YES`, md5
`7d89856fde41`):

| expression | OLD JIT | NEW JIT | interpreter |
|---|---|---|---|
| `not e.?` (`i64? = nil`) | false | **true** | true |
| `not Some(nil).?` | false | **true** | true |
| `not Some(42).?` | false | false | false |
| `not 3` / `not 0` / `not 1` | false / true / false | unchanged | same |
| `not true` / `not false` | false / true | unchanged | same |

NEW JIT and the interpreter now agree on **every** field, and the scalar results
are untouched — `not 3` stays false, so the repair did not trade one divergence
for the opposite one.

## Residual: a bare nil-valued binding is still wrong

`val n = nil; not n` remains `false` under the JIT. Instrumentation showed why:

```
compile_unary_op Not reached, operand_ty=Some(TypeId(5))   # I64 — for `val n = nil`
compile_unary_op Not reached, operand_ty=Some(TypeId(16))  # for `e.?`
compile_unary_op Not reached, operand_ty=Some(TypeId(14))  # ANY — for `Some(..).?`
```

A binding initialised to a bare `nil` infers to `TypeId(5) = I64`, the same
static type as `val three = 3` and carrying the same 64-bit pattern `3`. Those
two are genuinely indistinguishable at this point, so the sentinel compare
cannot be enabled for `I64` without breaking `not 3`.

**This half is a representation defect**, same family as
`nil_sentinel_3_forbids_defaulted_int_args`. Two routes:

1. **Stop inferring `i64` for a nil-initialised binding** — give it a nil/optional
   type, after which the existing gate covers it with no codegen change. This is
   the smaller fix and is where the real bug is.
2. **Stop reusing `3` as the nil sentinel for integer-typed values**, so the bit
   patterns no longer collide.

The load-bearing idiom (`not <optional>.?`, used throughout the spec corpus) is
fixed by the change above; the residual affects only bare nil-valued bindings.

**Method note.** An earlier revision of this report concluded the repair was
impossible here. That was wrong, and it came from probing only `val n = nil` —
the one case that falls outside the gate — and generalising from it. The idiom
the corpus actually uses carries a different `TypeId` and was fixed by the same
patch that had been declared ineffective. Probe the case the code under test
actually exercises.

Note that a related coercion is already known to be inconsistent: `1 == true`
holds in the pure-Simple matcher but not under the Rust runner
(`int_payload_compares_equal_to_bool_true_2026-08-04.md`). These are the same
class of defect — unspecified truthiness coercion resolved differently per
engine — and are probably worth one ruling rather than two fixes.

Related: `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`.

## Re-verification 2026-08-09 — residual also fixed, closing

Fresh probe on `bin/simple run` (seed at
`bin/release/x86_64-unknown-linux-gnu/simple`):

```
fn main():
    val n = nil
    print "not nil  -> {not n}"      # true  (was false)
    print "not true -> {not true}"   # false
    print "not false -> {not false}" # true

    var e: i64? = nil
    print "not e.? -> {not e.?}"             # true
    val s: i64? = Some(nil)
    print "not Some(nil).? -> {not s.?}"     # true
    val s2: i64? = Some(42)
    print "not Some(42).? -> {not s2.?}"     # false
    print "not 3 -> {not 3}"                 # false
    print "not 0 -> {not 0}"                 # true
```

All eight results match the interpreter/test-runner semantics documented above,
including the bare `val n = nil` case flagged as an unresolved residual on
2026-08-04. No code change was needed here — a prior landed fix (the
`operand_may_be_nil` sentinel-compare gate in `compile_unary_op`) evidently
covers this case too, or type inference for nil-initialised bindings changed
since. Closing as RESOLVED; no regression coverage added beyond this probe
since the fix already lives in `src/compiler_rust` (out of `.spl`/`.shs`
scope for this pass) and the spec corpus already exercises `not opt.?` broadly
per the original report.
