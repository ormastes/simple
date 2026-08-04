# `not nil` yields `false` in the `run` engine but `true` under the test runner

**Status:** OPEN (engine divergence — unary `not` over `nil` / `T?`).
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

## Why it cannot be fixed in `compile_unary_op`

The obvious repair — also compare against the nil sentinel 3 — was implemented,
built, and **disproved**. Instrumenting the function shows every `not` operand
in the repro arriving as the same static type:

```
compile_unary_op Not reached, operand_ty=Some(TypeId(5))  x4   # I64
compile_unary_op Not reached, operand_ty=Some(TypeId(1))  x2   # BOOL
```

`TypeId(5)` is `I64`, and it covers **both** `val n = nil` and `val three = 3`.
At this point in codegen, `not nil` and `not 3` are indistinguishable: same
static type, and the same 64-bit pattern `3`. Any comparison that makes
`not nil` true necessarily makes `not 3` true as well — trading one divergence
for the opposite one. The attempted fix was reverted; it is not in the tree.

Gating on the static type does not work either, precisely because a nil-valued
binding is typed `I64` rather than nil/optional/any.

## Fix direction

This is a **representation** defect, not a `not`-lowering defect, and it is the
same family as `nil_sentinel_3_forbids_defaulted_int_args`. Two viable routes:

1. **Preserve nil-ability in the JIT's static types** so codegen can tell a
   possibly-tagged operand from a raw integer — then the sentinel compare can be
   emitted only where it is sound. This is the smaller change if `vreg_types`
   can carry optional-ness.
2. **Stop reusing `3` as the nil sentinel for values statically typed as
   integers**, so the bit patterns no longer collide.

Whichever is chosen, `not` must end up agreeing across all three engines. Decide
the truthiness rule once — `nil` ⇒ absent ⇒ `not nil` is `true`, which is what
two of the three engines and the whole spec corpus already assume — rather than
leaving it engine-dependent.

Note that a related coercion is already known to be inconsistent: `1 == true`
holds in the pure-Simple matcher but not under the Rust runner
(`int_payload_compares_equal_to_bool_true_2026-08-04.md`). These are the same
class of defect — unspecified truthiness coercion resolved differently per
engine — and are probably worth one ruling rather than two fixes.

Related: `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`.
