# native-build: `?` on `Option` silently miscompiles (treated as `Result`)

**Severity:** high (silent-wrong on BOTH oracle and native — no diagnostic)
**Found:** 2026-07-14, errhandling lane
**Backend:** native-build `--entry` and seed interpreter

## Symptom

Applying `?` to an `i64?`/`Option` value inside a `Result`-returning function
produces wrong values with no diagnostic on either backend (observed rc 208
oracle / 209 native for a case that should be deterministic).

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` ~L972
`lower_try_expr` unconditionally treats the `?` base as a `Result`
(`rt_enum_discriminant`/`rt_enum_payload`), with no branch for `Optional` types.

## Fix direction

Branch on `base.type_` (reliable by MIR-lowering time; HIR lowering runs before
type inference, so this cannot be fixed in the HIR files). For an `Optional`
base, `?` should early-return `nil`/`None` on the none case and unwrap the
payload otherwise — or, if the enclosing function's return type is not
Option-compatible, **loud-fail** at build time rather than emit the Result path.

## Reproduce

`/tmp/wt_errhandling/` probes (Option `?` alongside Result `?`).
