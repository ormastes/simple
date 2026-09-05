# MIR lowering has no case for 9 of 26 `HirTypeKind` variants — hits a fatal wildcard arm on the canonical redeploy-gate smoke fixture

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Found while verifying the `me`-receiver fix (`ea198ba3e60`,
`MirToLlvm.llvm_type_text`/`llvm_function_symbol_name`/`native_int`) with a
fresh stage-2 self-hosted binary from an ad-hoc incremental bootstrap
(`build/bootstrap-adhoc-20260805-user`, stage 2: 727 compiled / 0 failed).

## The `me`-receiver fix is confirmed working

`scripts/check/cert/redeploy_gate/fixtures/p2_add.spl` (the repo's own
canonical smoke fixture) built through method dispatch on `.len()` and
several other calls with **no SIGILL, no nil-receiver crash, no exit 132** —
the original blocker-symptom this fix targeted is gone. Full trace has zero
occurrences of `SIGILL` / `nil receiver` / `field access on nil`.

## New, different, backend-agnostic failure

The same fixture now fails later, in `lower_type`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl:698`), identically
under both `--backend llvm` and `--backend cranelift`:

```
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x1800000007>
error: in-process native-build: MIR lowering error: unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x1800000007>
```

Real (non-piped) exit code is `1` — a clean compile-time fatal error, not a
crash. It fires right after `[mir-method-call] ... method=len` finishes
dispatch (`xs.len()` on the fixture's `[i64]` local), so the type being
lowered is very likely the receiver/element type of an array method call.

## Root cause: `lower_type`'s match is missing 9 of 26 declared variants

`HirTypeKind` (`src/compiler/20.hir/hir_types.spl:736`) declares 26 variants.
`lower_type`'s match (`function_lowering.spl:614-699`) has explicit arms for
17: `Int, Float, Bool, Char, Str, Unit, Tuple, Array, Dict, Ref, Ptr,
Optional, Result, Union, Named, Infer, Never, Error`. The remaining 9 fall
through to the `case _:` wildcard arm, which is **fatal** (unlike the
`Error`/`Infer` arms, which are fail-soft or explicitly labeled):

`Slice, TypeParam, DynTrait, Function, Projection, Isolated, Any, Tensor,
Layer`

`disc=-1` from `rt_enum_discriminant(type_.kind)` inside the error message
itself suggests the discriminant lookup also fails for whichever of these
hits the arm — has not been narrowed further to the exact variant (would
need an instrumented rebuild; not done this pass).

## Severity and disposition

This blocks `native-build` (both backends) on the repo's own canonical
smoke-test fixture today, via the self-hosted compiler's own MIR lowering —
independent of the `me`-receiver fix, which is confirmed correct.

**Not fixed this pass** — filed per repo convention (record a concrete bug
rather than silently working around it). Candidate fixes, either:
1. Narrow: add the exact triggering variant (most likely `Slice` or
   `Function`, given the `.len()`-call trigger) with fail-soft handling
   matching the existing `Error` case.
2. Broad: audit all 9 unhandled variants and give each a real MIR lowering
   or an explicit fail-soft/fatal decision, rather than one undifferentiated
   wildcard arm silently swallowing 9 different type kinds.

Belongs in `src/compiler/50.mir/_MirLowering/function_lowering.spl` (and
possibly upstream in HIR type inference if the real issue is that one of
these variants shouldn't reach MIR lowering unresolved at all — same shape
as the sibling `Infer` case documented in
`native_build_self_hosted_mir_infer_type_crash_2026-07-30.md`).
