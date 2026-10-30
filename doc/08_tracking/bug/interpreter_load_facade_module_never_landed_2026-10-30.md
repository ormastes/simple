# interpreter_load_facade_spec imports a facade module that never landed on release/1.0.0

Status: OPEN. The spec is tagged `@tag:in-development` until the module lands.
Found by the Lunar interpreter sweep (2026-10-30).

## Symptom

`test/01_unit/compiler/interp/interpreter_load_facade_spec.spl` fails with 0 of 8
examples executed:

    error: runtime: Module "compiler.interp" does not export 'load_facade'

## Root cause

The spec imports `compiler.interp.load_facade.{InterpreterLoadErrorV1,
InterpreterLoadResolverIdentityV1, InterpreterLoadSnapshotIdentityV1,
interpreter_load_plan_v1}`. On release/1.0.0, `src/compiler/95.interp/load_facade/`
holds only `interpreter_load_facade_v1.spl`, which defines none of those symbols.
It has no `__init__.spl`, `facade.spl`, or `contracts.spl`. Those three files exist
only in the WIP snapshot commit `a7e1304c197` ("chore(wip): preserve uncommitted
peer-session work products"), which is reachable only from
`origin/archive/aop-wip-2026-09-03`. The spec landed and the implementation did not.
`test/02_integration/compiler/interpreter_loader_package_image_entrypoint_spec.spl`
and `test/01_unit/compiler/loader/interpreter_loader_production_entrypoint_contract_test.shs`
also expect `load_facade/__init__.spl`.

## Unblock condition

Review the facade from `a7e1304c197` and land it (about 225 lines of unreviewed
peer-session WIP that another session owns), or rewrite the spec against
`interpreter_load_facade_v1.spl`. When it lands, remove the `@tag:in-development`
line from the spec.
