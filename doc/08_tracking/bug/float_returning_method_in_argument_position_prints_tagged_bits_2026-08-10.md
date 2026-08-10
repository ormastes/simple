# A float-returning method used directly as a call argument prints raw tagged bits

- **Date:** 2026-08-10
- **Status:** OPEN — found while fixing
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

## Related

- `doc/08_tracking/bug/numeric_builtins_hardcode_i64_result_type_2026-08-10.md`
  (found alongside; the `sqrt`/`floor`/`ceil`/`pow` free-function defect there is
  a *third*, separate mechanism — an integer-ABI call to libm)
- `3f4486b45fa` — the print-drop defect with the same direct-argument shape
- `scripts/check/check-native-print-stdout-oracle.shs`
