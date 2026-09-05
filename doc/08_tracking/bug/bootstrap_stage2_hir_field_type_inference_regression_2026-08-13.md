# Stage2 HIR field-type inference regression

## Status

Open. The isolated Stage2 bootstrap campaign produced no admitted compiler.

## Evidence

The provenance-isolated Cranelift Stage2 campaign
`perf-stage2-f96fe5b37fd-20260813` ran from the separate clean authority
`/mnt/data/perf-feature-integrated-current` (not the concurrently edited shared
worktree). It ended `exit-1` during native build with 86
HIR lowering failures of the form `cannot infer field type`, spanning compiler
and library modules. Representative failures include `ANY` fields such as
`kind`, `name`, `symbol`, and `line`, plus concrete receiver fields.

## Impact

No Stage2 admission, sanity, or provenance receipt exists. The deployed
`bin/simple` remains non-admissible for release evidence; do not fall back to
it for mission-critical verification.

## Next owner

Restore nominal imported-type provenance centrally in the Rust HIR
owner-resolution/import-map chain. A per-module cast, annotation sweep, or
receiver-blind field fallback would hide the shared regression and is not an
acceptable bootstrap repair.

The focused failure is an imported `Attribute { args: [Expr] }`: lowering the
loop variable from `attr.args` loses the owner-qualified `Expr` type and turns
`arg.kind` into an `ANY` access. The repair must resolve an imported authored
spelling to its exact canonical layout owner before accepting a local import
placeholder, then register that owner and its recursively resolved fields.

## Remaining collision-safe integration requirement

The shared resolver's current partial materialization path is sufficient only
when a bare nominal name has one global owner. It is not a complete repair for
two imported `Foo` layouts: declaration-file metadata is currently keyed by
bare name, and field lookup can reduce a receiver `TypeId` back to that bare
spelling. The completed repair must retain `TypeId -> canonical owner` metadata
at class/struct registration (including imported materialization) and use it
for field layout lookup. A regression must prove that two same-named imported
types resolve different field index/types from their own receiver TypeIds.
