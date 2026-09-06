# Numeric builtins hard-code an `i64` result type, printing float answers as raw IEEE bits

- **Date:** 2026-08-10
- **Status:** DEFECT A **FIXED**; DEFECT B **FIXED**; DEFECT C **FIXED**
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

## Defect B — `sqrt`/`floor`/`ceil`/`pow` compute genuine garbage (FIXED)

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

### Fix

**A float-ABI external-call path already existed and did not have to be built.**
`codegen/runtime_sffi.rs::RUNTIME_FUNCS` declares real `F64` signatures for
`rt_math_sqrt` / `rt_math_floor` / `rt_math_ceil` / `rt_math_pow`;
`codegen/instr/calls.rs::adapt_args_to_signature` converts arguments to the
declared types at the call site; and the `f64 **` operator in
`codegen/instr/core.rs` already calls `rt_math_pow` exactly this way. All four
symbols are also registered in the interpreter (`interpreter_extern/mod.rs`) and
exist as `extern "C"` `f64` functions in the Rust runtime
(`runtime/src/value/sffi/math.rs`). So the fix routes these four builtins onto
that existing path rather than teaching the generic integer call about floats.

`mir/lower/lowering_expr_builtin.rs::lower_libm_math` (new, sibling of
`lower_min_max_abs`) lowers each of the four to `Cast`-to-`f64` on every
argument, a `MirInst::Call` to the matching `rt_math_*` symbol, and a `Cast`
back to the `expr_ty` that Defect A's `numeric_builtin_result_ty` already
derived from the arguments. Integer callers therefore keep integer results
(`sqrt(16)` => `4`), matching the interpreter-fallback lane exactly.
`codegen/instr/body.rs::build_vreg_types` gains the matching `-> F64` stamp for
those four call targets, without which a directly-printed `sqrt(16.0)` has an
untyped result VReg and renders the float as an integer.

**Same Rust-seed rationale as Defect A:** this name-to-emitted-call mapping
exists only in the seed's MIR lowering; no pure-Simple file expresses it, and
MIR lowering is one layer upstream of every backend, so it is a single fix
point rather than a per-backend one.

Measured, same probe, same binary lineage (private `CARGO_TARGET_DIR`, debug
`simple-driver`), both lanes, via typed locals:

| expression | before | after |
|---|---|---|
| `sqrt(16.0)` | `6.39e-310`-class denormal (run-varying) | `4.0` |
| `sqrt(16)` | `5470854845600` (interp) / `3872221041824` (jit) | `4` |
| `floor(2.7)` | `2.7` | `2.0` |
| `ceil(2.1)` | denormal garbage | `3.0` |
| `pow(2.0, 3.0)` | denormal garbage | `8.0` |
| `pow(2, 3)` | `255` | `8` |
| `floor(17)` / `ceil(12)` | `6083089011872` / `4108981114016` | `17` / `12` |

**Native lane, not fixed and not regressed:** `native-build` (the pure-Simple
driver, with or without `--entry-closure`) rejects all four names outright —
`HIR lowering error: unresolved name: ceil` — identically before and after this
change (15 `unresolved name` diagnostics in both logs). That is a separate,
pre-existing gap in the pure-Simple driver's builtin table, not part of this
defect, and it is why the fence covers the interpreter, JIT, and
interpreter-fallback lanes only.

## Defect C — the interpreter-fallback lane truncated floats (FIXED)

There is a **third lane**, distinct from both above, found only by measuring the
Part-2 shadow deletion rather than assuming it was safe.

When a module drops to the **whole-module interpreter fallback**, the numeric
builtins are served by `interpreter_extern/math.rs`, not by the MIR lowering the
interpreter/JIT lanes exercise. Every one of those handlers called `as_int()` on
its arguments, which **truncates** floats:

```
min(1.5, 2.5)  =>  1        (in the fallback lane)
```

and `sqrt`/`floor`/`ceil`/`pow` were integer-only there as well.

This was invisible because `src/lib/nogc_sync_mut/runtime_wrappers.spl`
accidentally **shadowed** `min`/`max`/`abs` with pure-Simple reimplementations
that happened to be float-tolerant, so callers never reached `math.rs`.

**This is the reroute hazard, caught in the act.** Deleting the shadows (Part 2)
reroutes callers *into* `math.rs`. Measured on the unmodified tree, the same
probe printed `1.5`; with the shadows deleted and `math.rs` untouched it printed
`1`. Landing the deletion alone would have introduced a silent float-truncation
regression while looking like pure dead-code removal.

**Fix:** `math.rs` now takes a float path whenever any argument is float
(widening integers, so `pow(2.0, 3)` works), and keeps the exact previous
behaviour for all-integer calls. The integer `pow` additionally rejects a
negative exponent instead of casting it to `u32`, where it wrapped to a huge
unsigned value and then panicked or overflowed.

## Related fourth finding — float results lose their type in direct argument position

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
negative control that proves the harness can fail. The four Defect-B cases were
XFAIL rows; they are now positive assertions, joined by negative-argument
`floor`/`ceil` rows, the four integer-argument rows (the group that separated B
from A), and typed-local forms. **48 assertions, PASS** on the fixed binary (was
32 with 8 XFAILs). Revert-proof: the same script against the pre-fix binary
reports `FAIL — 48 assertions checked, 24 wrong value(s)`, exit 1, with the
specific wrong values tabulated above.

## Related

- `doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md`
