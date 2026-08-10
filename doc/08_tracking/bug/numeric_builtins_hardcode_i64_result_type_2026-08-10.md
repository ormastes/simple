# Numeric builtins hard-code an `i64` result type, printing float answers as raw IEEE bits

- **Date:** 2026-08-10
- **Status:** DEFECT A **FIXED**; DEFECT B **OPEN** (independent, filed below)
- **Lanes measured:** interpreter, JIT (`SIMPLE_JIT_STRICT=1`)
- **Class:** silent wrong-value / type mislabel
- **Fence:** `scripts/check/check-numeric-builtin-result-type.shs`

## Symptom

```
print min(1.5, 2.5)   =>  4609434218613702656
```

`4609434218613702656` is `0x3FF8000000000000` — the exact IEEE-754 bit pattern
of `1.5`, the **correct answer**. The builtin computed the right number; only
the result *type* was wrong, so `print` rendered the bits as an integer.

## Defect A — root cause (FIXED)

`src/compiler_rust/compiler/src/hir/lower/expr/calls.rs`, `lower_utility_builtin`:

```rust
"abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
    Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?))
}
```

`TypeId::I64` unconditionally, for all seven builtins, regardless of argument
types.

**This is a Rust seed edit for a HIR-lowering defect with no `.spl` site.** The
hard-coded `TypeId::I64` exists only in the seed's HIR lowering; there is no
pure-Simple file that expresses this mapping, so the repo's "fix `.spl` not
Rust" default does not apply here — the defect has no `.spl` representation to
fix.

**Fix:** derive the result type from the lowered argument types —
floating point if any argument is floating point (widening `f32` → `f64`),
otherwise `i64` exactly as before. `TypeId::ANY` arguments deliberately do not
force a float, so integer callers with incomplete inference are unchanged.

### Why the computation was already right for `min`/`max`/`abs`

MIR lowering (`mir/lower/lowering_expr_builtin.rs`, `lower_min_max_abs`) lowers
these three to a compare plus a **typed** select, and codegen picks `fcmp` vs
`icmp` off `vreg_types`. Measured proof that this is a genuine float compare and
not an accident of IEEE bit ordering — negative arguments, on the *broken*
build, via a typed local:

| expression | via `val x: f64` (broken build) | direct `print` (broken build) |
|---|---|---|
| `min(-1.5, 2.5)` | `-1.5` ✓ | raw bits |
| `min(-1.5, -2.5)` | `-2.5` ✓ | raw bits |
| `max(-1.5, -2.5)` | `-1.5` ✓ | raw bits |
| `abs(-1.5)` | `1.5` ✓ | raw bits |

Positive-only testing would have been fail-open here: IEEE positive floats
order-correspond to their bit patterns, so an integer compare would also have
produced the right answer for positives. The negative rows are what proved it.

## Defect B — `sqrt`/`floor`/`ceil`/`pow` compute genuine garbage (OPEN)

Reported as "possible uninitialised read: `sqrt(16.0)` returned different
garbage on consecutive runs". Confirmed real, **independent of Defect A**, and
the mechanism is now identified — it is not uninitialised memory.

These four names are **not** handled by `lower_min_max_abs`. They fall through
to a generic external `MirInst::Call` to symbols literally named
`sqrt`/`floor`/`ceil`/`pow`, which link to **libm**. libm's `sqrt` takes and
returns a `double` (xmm0), but the call is emitted with the **integer ABI** —
arguments in integer registers, result read from `rax`, which libm never wrote.
The "different garbage on consecutive runs" is therefore stale register/stack
contents, which is why it varies per run and looks like heap addresses.

Measured, both lanes, direct `print`:

| call | run 1 | run 2 |
|---|---|---|
| `sqrt(16.0)` | `5138232905792` | `2391366438976` |
| `floor(1.7)` | `5138224137952` | `2391357671136` |
| `ceil(1.2)` | `5138224141664` | `2391357674848` |
| `pow(2.0, 3.0)` | `-6148914691236517206` | `-4557430888798830400` |

**Integer arguments are broken too**, which rules out the type mislabel as the
cause and was the measurement that separated B from A:

```
sqrt(16)  => 0                      (expected 4)
floor(17) => 3875235039328          (expected 17)
ceil(12)  => 3875235320560          (expected 12)
pow(2, 3) => -9187201950435737472   (expected 8)
```

`sqrt(16) => 0` is the tell: libm returned `4.0` in `xmm0` and the integer
return register `rax` was zero.

The comment already in `lower_min_max_abs` asserts that these four "map to real
libm symbols" — they do, but **not with a compatible ABI**, so that assumption
is where the defect lives.

**Fix shape (not done here):** extend `lower_min_max_abs` to cover
`sqrt`/`floor`/`ceil`/`pow` with float-typed lowering — the same layer, upstream
of every backend. The method forms (`x.sqrt()`, `x.floor()`) already lower
correctly through `codegen/instr/methods.rs` (`builder.ins().sqrt` / `.floor`),
so a working float path exists to route to.

## Related third finding — float results lose their type in direct argument position

Independent of both, and **not fixed here**:

```
val b: f64 = 16.0
print b.sqrt()        =>  577023702256844800
val c: f64 = b.sqrt()
print c               =>  4.0
```

`577023702256844800` is `bits(4.0) / 8` — the tagged-float representation
(`>> 3`) reaching `print` un-untagged. The computation is correct; the type is
lost when a float-returning method is used directly as a call argument. Filed
here for the record; it needs its own change.

## Verification

`scripts/check/check-numeric-builtin-result-type.shs` — asserts computed
**values** (not existence) across the interpreter and JIT lanes, with negative
arguments, integer-caller regression controls, a typed-local control, and a
negative control that proves the harness can fail. The four Defect-B float cases
are asserted as XFAIL rows: the script fails if one of them starts passing
without the XFAIL list being updated, so the open defect cannot be silently
fixed or silently forgotten.

## Related

- `doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md`
