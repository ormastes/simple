# Cranelift rejects every `-> f64`/`-> f32` function under SIMPLE_BOOTSTRAP=1

- **Status:** fixed in source, NOT verified green (needs a Stage 2 rebuild).
- **Modules seen failing:** `lib.common.math.math`, `lib.nogc_sync_mut.simd`,
  `lib.nogc_async_mut.sosix.host_facade`, `compiler.frontend.parser_types_utils`.

## Symptom

```
cranelift: AOT define_function error: Verifier errors:
- inst7 (return v5): result 0 has type f64, must match function signature of i64
```

## Repro (red, producer p2shard-10 Stage 2)

Producer `simple-boot-p2shard/build/bootstrap-p2shard-10/stage2/aarch64-unknown-linux-gnu/simple`,
runtime capsule `db10b27e...ccf6`, `SIMPLE_BOOTSTRAP=1`, `native-build --backend cranelift
--runtime-bundle core-c-bootstrap --entry-closure`:

```simple
fn fr_d(x: i64) -> f64:
    1.5

fn main() -> i64:
    if fr_d(2) > 1.0: 0 else: 1
```

No `?`, match, Option, trait or generic is needed: ANY declared float return
fails (`a + t * (b - a)`, `if x < 0.0: 0.0 - x else: x`, and an
`unsafe: rt_math_sqrt(x)` tail all fail the same way).

## Root cause

`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` (the
`if fn_.has_return_type:` block in `lower_function`): under
`ambient_bootstrap_enabled()` a declared return was kept only for
`Str | Bool`; everything else fell to `bootstrap_builtin_return_type`, i.e.
`i64`. So the definition's `HirFunction.return_type`, hence
`MirSignature.return_type`, hence the Cranelift signature
(`build_signature`/`sig_type_to_cl`) was `i64`, while the body's tail value is
still `F64` (typed float loads/`fconst`). `SIMPLE_MIRB_TRACE=1` confirms it:
`lower_type` sees the Float kind for the params and the Int kind for the
return of `fr_d`.

Callers were already on the declared type: `declared_callable_type`
(`module_callable_types.spl`) lowers the return unconditionally, so a caller
expected `f64` from a definition that was published as `i64` — the definition
and its call sites disagreed. Ints absorb this (signatures widen to i64);
floats cannot.

## Fix

Preserve `HirTypeKind.Float(_)` alongside `Str | Bool` in that bootstrap arm,
so the definition, its MIR signature and its callers agree on `f32`/`f64`.
Ints, aggregates and Unit stay on the legacy fallback (W92 history).

Regression spec (written, not executed):
`test/01_unit/compiler/hir/bootstrap_declared_float_return_spec.spl`.

No source workaround exists at the failing sites: any annotated float return
is erased, and dropping the annotation infers `i64` too.

Unrelated, not on the active path: the flat-decl tag table
`bootstrap_hir_type_from_tag` (`module_declarations_bootstrap.spl`) has no
float tag either.

## `compiler.mir._MirLoweringExpr.expr_dispatch` (Phase-3 run-16): NOT this bug

`inst70 (return v53): arguments of return must match function signature` is
Cranelift's **arity** message, a different verifier class from the type
message above. The instruction carries one operand (`v53`), so the signature
has **zero** returns: a valued return into a void signature. The float erasure
produces the opposite situation (a valued signature), so it cannot cause
inst70.

The function is unidentified. A shape that fits: a method the bootstrap return
scan classified as Unit (unannotated, no value `return` found) whose MIR still
emits `Ret(Some(v))`, for example from an untyped tail value (commit
`7888d8141a1` touched that path). Unconfirmed.

Separate and also unfixed: `-> ()` handling in bootstrap mode is broken in its
own way. The only `-> ()` method in that module,
`emit_pending_finally_for_transfer`, is not `Str | Bool` either, so it is
published as `-> i64`. Probes of its shape with the same producer fail before
codegen with `E-SFFI-016: missing return in non-unit function 'run_pending'`,
both for a declared `-> ()` and for an unannotated method containing
`return ()` (the return scan counts `()` as a value return). That is not the
inst70 shape. Unit was deliberately NOT added to the preserved set: under a
Unit signature, `return ()` still lowers to `Ret(Some(unit temp))`, which
`cl_translate_terminator` would emit as a valued return into a void
signature. It needs its own fix and proof.
