# A float-returning method used directly as a call argument prints raw tagged bits

- **Date:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  below as stated — see "Resolution" at the bottom. It is not the desugar
  rebuild and not the print/`to_text` coercion; it is a missing HIR **result
  type** for the float math methods, one layer earlier than both. Fenced by
  `scripts/check/check-float-method-argument-position.shs`.
- **Status (original):** OPEN — found while fixing
  `numeric_builtins_hardcode_i64_result_type_2026-08-10.md`, filed separately
  because it is a different layer and a different mechanism.
- **Lanes:** interpreter and JIT (`SIMPLE_JIT_STRICT=1`) — both.
- **Class:** silent wrong-value / type loss in argument position.

## Symptom

```
fn main():
    val b: f64 = 16.0
    print b.sqrt()        # => 577023702256844800
    val c: f64 = b.sqrt()
    print c               # => 4.0
```

Same method, same receiver, two different printed results. Binding the call to a
typed local prints the correct `4.0`; using it **directly as the argument to
`print`** prints an enormous integer.

## The number is decodable, and that is the whole diagnosis

`577023702256844800` is not garbage and not a pointer:

```
bits(4.0)          = 0x4010000000000000 = 4616189618054758400
4616189618054758400 / 8                 =  577023702256844800   <-- printed
```

Exactly `bits / 8`, i.e. the value shifted right by 3. That is the **tagged
float representation** (the `(bits >> 3) << 3` tagging used for boxed floats)
reaching `print` without being untagged. Confirmed across four different
methods, all exactly `bits/8`:

| expression | printed | `printed * 8` | decodes to |
|---|---|---|---|
| `(16.0).sqrt()` | 577023702256844800 | 0x4010000000000000 | `4.0` |
| `(1.7).floor()` | 575897802350002176 | 0x3FF0000000000000 | `1.0` |
| `(1.7).ceil()` | 576460752303423488 | 0x4000000000000000 | `2.0` |
| `(-1.5).abs()` | 576179277326712832 | 0x3FF8000000000000 | `1.5` |

**The computation is correct in every case.** `sqrt`, `floor`, `ceil` and `abs`
all produced the right answer; only the untagging is missing on the path from a
method call straight into an argument slot.

## Why this is filed separately from the numeric-builtin defect

`numeric_builtins_hardcode_i64_result_type_2026-08-10.md` was a **HIR result
type** that was hard-coded to `TypeId::I64`. This one is different on both axes:

- it affects **methods** (`x.sqrt()`), not the free-function builtins;
- the underlying method lowering is already correct — `codegen/instr/methods.rs`
  emits real `builder.ins().sqrt` / `.floor` / `.fabs` — and the value survives
  intact when stored to a typed local. Only the direct-argument path loses it.

So it is not fixed by, and does not block, that change.

## Suspected relationship to the print-drop defect fixed today

This has the **same shape** as
`doc/08_tracking/bug/..._print_with_call_silently_drops_output_2026-08-10.md`,
fixed in `3f4486b45fa` ("preserve interpolated-string template text across
placeholder rebuild", touching
`src/compiler/10.frontend/desugar/placeholder_lambda.spl` and
`src/compiler/10.frontend/core/_AstExpr/accessors.spl`): in both, a **call
appearing directly in argument position** is mishandled, while the identical
call bound to a local first behaves correctly.

**Whoever picks this up should first determine whether it is the same root cause
or a sibling.** Concretely: check whether the desugar/placeholder rebuild path
that `3f4486b45fa` repaired also drops the *type* annotation (not just the
template text) when the argument is a method call, or whether the untagging is
lost later, in the print/`to_text` coercion. The two hypotheses are
distinguishable — if it is the desugar path, the fix lands in the same
pure-Simple frontend files as `3f4486b45fa`; if it is the coercion, it lands in
the argument-coercion path near where `rt_value_to_string` decides whether to
unbox.

Note the two defects were fixed/found on the same day, so `3f4486b45fa` did NOT
fix this one — the measurements above were taken on a binary built from
`origin/main` **after** that commit.

## Reproduction

```
fn main():
    val b: f64 = 16.0
    print b.sqrt()          # WRONG: 577023702256844800
    val c: f64 = b.sqrt()
    print c                 # RIGHT: 4.0
```

Both lanes:
```
simple run repro.spl
SIMPLE_JIT_STRICT=1 simple repro.spl
```
`SIMPLE_JIT_STRICT=1` is required on the JIT lane — without it a JIT failure
falls back to the interpreter and the lane reads as a pass without ever having
run the JIT.

## Resolution (2026-08-10)

**Which hypothesis held: neither, exactly.** The filing offered (a) the
desugar/placeholder rebuild dropping the type annotation, or (b) loss in the
argument-coercion path near `rt_value_to_string`. The real cause is upstream of
both: the type annotation was never *dropped*, it was **never produced**.

`Lowerer::lookup_method_return_type`
(`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`, the `TypeId::ANY`
fall-through at the end) knew the result type of the numeric CONVERSION methods
(`to_int`, `to_f64`, ...) but had no entry for the float MATH methods. Those are
compiler intrinsics lowered inline by
`codegen/instr/methods.rs:199` — `matches!(method, "sqrt" | "abs" | "floor" |
"ceil" | "round")` -> `builder.ins().sqrt / fabs / floor / ceil / nearest` — so
they have no `method_return_types` registry entry and fell through to
`TypeId::ANY`.

The instruction produces a **raw unboxed f64**, but an `ANY`-typed expression is
assumed to be an already-tagged `RuntimeValue`. MIR's print lowering
(`mir/lower/lowering_expr_builtin.rs`,
`needs_float_boxing = matches!(arg.ty, TypeId::F32 | TypeId::F64)`) therefore
emitted no `BoxFloat`, and `rt_print_value` applied `as_int()` — `raw >> 3` — to
the IEEE bit pattern. That is the `bits / 8` in the table above, and it is why
the number was decodable: nothing was corrupted, the value was simply read
through the wrong tag.

**Evidence that discriminated the hypotheses.** The desugar hypothesis predicts
the defect is specific to argument position. It is not: `b.sqrt().to_text()`
(no argument position at all — the float call is a *receiver*) printed the same
`577023702256844800`, and `b.sqrt() + 1.0` printed `577164439745200128`, which
is `bits(5.0) / 8` — the ADDITION was performed correctly on the float and the
tag was lost afterwards. A rebuild that dropped an annotation in argument
position cannot explain either. Conversely the coercion hypothesis predicts the
value arrives at the printer correctly typed and is mis-rendered; but the
printer's decision is driven entirely by the tag on the incoming word, and the
word had tag `000` (integer) because no boxing instruction was ever emitted.
Both point one layer earlier, at the type stamp. The exact precedent was
already in the same function: the `to_float`/`to_f64` case immediately above the
new one, added for the identical mechanism on 2026-07-29 (lane FLOATBOX).

**Layer: seed-side (Rust), not `.spl`.** The repo default is to fix in
pure-Simple, but this is the seed's own HIR lowerer: the function, the
`TypeId::ANY` fall-through, and the `needs_float_boxing` consumer all live in
`src/compiler_rust`. There is no pure-Simple surface that determines the HIR
result type for a seed-lowered intrinsic, so a `.spl` change could not have
fixed it.

**Fix.** One `matches!` arm in `lookup_method_return_type` returning the
receiver's float type for `sqrt | abs | floor | ceil | round` on an `F32`/`F64`
receiver. The list is deliberately exactly the codegen inline set, and it is
restricted to float receivers: stamping a type on a method with no lowering
would tell MIR to unbox a value the callee never produced.

**Verification.** `scripts/check/check-float-method-argument-position.shs`, 34
computed-value assertions across the interpreter and JIT lanes (JIT with
`SIMPLE_JIT_STRICT=1`). Negative control by binary pair, same script: **26 of 34
FAIL** on a binary built from unmodified `bb43fac0cf5`, **34 of 34 PASS** on the
same tree with the one-arm fix. The 8 rows that pass on both are the typed-local
and conversion-method controls, which is exactly the expected split.
`check-numeric-builtin-result-type.shs` stays green and unmodified at 48/48.

**Native lane: NOT fixed, and not regressed.** Native still prints garbage for
`print b.sqrt()` — but so does `print b` for a plain `val b: f64 = 16.0`, on the
unmodified binary as well. The native lane cannot render any `f64` at all; filed
as `native_lane_prints_every_f64_as_denormal_garbage_2026-08-10.md`.

## Family enumerated (measured, not assumed)

Scoping the fix turned up two adjacent defects that are NOT this one and are
filed separately rather than folded in:

- `float_literal_receiver_method_call_returns_receiver_2026-08-10.md` —
  `print (16.0).sqrt()` prints `16.0`: the method is not applied at all. A
  well-formed, correctly-boxed *receiver*, so it is a resolution failure, not a
  boxing failure.
- `float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md` —
  `f64.trunc`, `f64.sin`, `f64.pow`, `f64.max`, `i64.abs` do not resolve at all
  ("Function 'f64.sin' not found"). This is why the fix is scoped to five
  methods and to float receivers.

## Related

- `doc/08_tracking/bug/numeric_builtins_hardcode_i64_result_type_2026-08-10.md`
  (found alongside; the `sqrt`/`floor`/`ceil`/`pow` free-function defect there is
  a *third*, separate mechanism — an integer-ABI call to libm)
- `3f4486b45fa` — the print-drop defect with the same direct-argument shape
- `scripts/check/check-native-print-stdout-oracle.shs`
