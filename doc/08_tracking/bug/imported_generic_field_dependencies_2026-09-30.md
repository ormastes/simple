# Imported composite fields omit generic argument dependencies

Status: isolated source fix; rebuilt-producer qualification pending.

## Actual failure and minimal reproductions

Windows Phase 3 using retained pure-Simple producer
`0be6e4c2a802e4fa7993fde80003eb87ffae097e564adb82ab4c937bbc640161`
and frozen source `4a5a4ca1576177c28b84b4e0f276c8160e99259d` failed in HIR.
The complete diagnostics are in
`D:/dev/simple-windows-corrected-early-phases-20260930-producer-hir-attempt1/stage3/compile.stderr.log`.
The summary's first twenty messages include `CompilerProfile`, `ParserModule`,
`ModuleSurfacesByName`, `HirModule`, `MirModule`, and dictionary arguments
`SymbolId`, `MirFunction`, `MirStatic`, `MirConstant`, and `MirTypeDef`.

Bounded grouping of the complete fatal diagnostics found 256 occurrences of
`HirContractBlock`, 99 `SymbolId`, 83 `ModuleSurfaceExportOrigin`, 70
`MirModule`, and 68 `HirModule`. These counts describe printed fatal rows,
not every underlying error: the driver caps rows per module.

Two minimal fixtures isolate the common defect without a bootstrap retry:

- A class with `profile: Profile?` imported only through an identity function
  fails HIR with unresolved `Profile` after 0.346 seconds.
- A class with `values: Dict<Key, Payload>` imported through an identity
  function fails HIR with unresolved `Key` and `Payload` after 0.658 seconds.

Plans, exact sources, producer binding and terminal logs are under
`D:/dev/windows-hir-type-owner-probes-20260930/optional-field-relative/` and
`map-field-relative/`. No live producer inputs or shared caches were changed.
Plain scalar callable, generic callable, and plain class-method controls all
passed HIR/MIR, then stopped at fixture native linking because their external
project root did not contain `src/runtime/runtime.c`. They establish HIR
controls only, not complete executable success.

## Cause and fix

`register_imported_symbol_inner` registers composite field dependencies before
projecting their HIR types. A nonempty scalar field projection takes the
outer name only: `Profile?` is projected as `Option`, while
`Dict<Key, Payload>` is projected as `Dict`. The `else` branch recursively
walks full types, but the scalar and array element branches skip generic
arguments. Type projection subsequently visits them and fails against the
importer's scope, attributing the error to an innocent importer.

Keep the existing scalar registration fast path and additionally walk its
named arguments using the existing recursive dependency collector. Resolve
each argument through the field owner's existing dependency resolver, including
explicit import aliases. For arrays, inspect the projected element's arguments.
This complements the earlier callable-signature correction; no missing leaf
imports, fake types, runtime hooks, or skipped errors are added.

## Prevention

`test/01_unit/compiler/hir/imported_generic_field_dependencies_spec.spl`
checks optional enum fields, dictionary arguments with an explicitly imported
alias, nested optional/generic arguments, and arrays of generic fields. Each
requires zero HIR errors, a nonempty lowered consumer, and owner-qualified
bindings. `test/fixtures/native/imported_generic_fields/` preserves a compact
native reproducer. Tests need the refreshed self-hosted producer/test runner.
Source review and whitespace checks do not constitute runtime verification.
