# native-build: `?` on `Option` silently miscompiles (treated as `Result`)

**Severity:** high (silent-wrong on BOTH oracle and native — no diagnostic)
**Found:** 2026-07-14, errhandling lane
**Status:** open
**Backend:** native-build `--entry` and seed interpreter

## Symptom

Applying `?` to an `i64?`/`Option` value inside a `Result`-returning function
produces wrong values with no diagnostic on either backend (observed rc 208
oracle / 209 native for a case that should be deterministic).

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` ~L972
`lower_try_expr` unconditionally treats the `?` base as a `Result`
(`rt_enum_discriminant`/`rt_enum_payload`), with no branch for `Optional` types.

## Blocking design findings (2026-07-15)

A reviewed prototype proved that `Option<T>` first needs canonical HIR lowering:
the flat bridge preserves `Option<i64>`, but `lower_named_kind` currently turns
it into unresolved `HirTypeKind.Error`. Direct-call recovery then works, while
unannotated locals and method-call results still lack authoritative container
metadata and would regress valid Result `?` if unknown operands were rejected.

The deeper blocker is the native flat primitive Option ABI. Raw `i64?` payloads
use their bare bits while nil uses sentinel `3`, so a valid present payload `3`
is indistinguishable from absence. Explicit `None` is separately constructed as
an enum with discriminant `1`, but `rt_is_none` recognizes sentinel `3` or a
legacy hashed discriminant, not ordinal `1`.

The fix therefore requires a uniform tagged/boxed Option representation (or an
equivalent non-colliding ABI) at producers and consumers, plus declared-type
provenance for direct calls, locals, and method calls. Acceptance must cover
raw/boxed zero, payload `3`, explicit `Some`/`None`, compatible and incompatible
return containers, unannotated locals, Result method calls, and unchanged
Result Ok/Err propagation. The incomplete MIR-only prototype was reverted.

## Reproduce

`/tmp/wt_errhandling/` probes (Option `?` alongside Result `?`).
