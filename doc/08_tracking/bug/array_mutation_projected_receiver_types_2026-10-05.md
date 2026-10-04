# Array mutation projections lose declared element types

Status: source repair reviewed; native verification pending.

## Observed failure

The pure-Simple producer `27ac2358f22f28c9a43ec3ab47ac3957d5e2b293fc8b44fc52e573512f0c4c69`
(source407be) failed the existing `native_array_mutation_methods.spl` build with
four unresolved methods: pop, sort, pop, clear. Retained full worker stderr:
`runtime/windows-restart-20261004/array-mutation-407be-trace2/artifact/tmp/native-build-stderr-20620-1.log`.
SHA256: `a3e11c3dacbd8cafdaeafed49b660a7ea23ba51df579d9162998a2269e08e483`.
The trace recognizes local452's pop receiver as an array, while locals511,
547 and556 lack the array dispatch event. Association with field pop and
indexed sort/pop/clear follows source order and writeback trace; local IDs
alone are not source-span evidence. Relay error repetition is not additional
failed cases.

## Cause and repair

Mutating receivers are prelowered once for writeback. The Field path remembers
array handle identity but omitted the actual field HIR type. Pop requires its
exact element type and refuses to guess i64. `receiver_declared_type` only
handles variable receivers, so it cannot recover that field declaration.

The mutating Index path separately calls `rt_array_get`; it marked a generic
runtime value but did not preserve the array-element declaration or register
nested array identity. The new shared projection helper records Array/Slice
identity and the full element HIR type only when the base declaration proves
that the selected element is itself Array/Slice. The ordinary indexed-read
path also retains that metadata, enabling consecutive index projections.

Field projections retain their declared Array/Slice HIR type. All affected
result locals are newly allocated; the neutral isolation/resource states match
the existing ordinary-field rule. No existing binding state is reset. No
receiver/index is evaluated again, and runtime handles, boxing/unboxing,
writeback, unknown-type rejection and scalar dispatch are unchanged.

## Verification

- Seven executable MIR metadata regressions: integer field, text slice field,
  nested text array, consecutive projections, scalar rejection, unknown-base
  rejection and invalid field index rejection. UNRUN.
- Six new native projected-mutation checks: field text pop, indexed text
  sort/pop/clear with single evaluation, field-index and double-index chains.
  UNRUN.
- Existing twenty-check `native_array_mutation_methods.spl` remains unchanged
  and is the primary real mutation oracle after rebuilding the pure-Simple
  producer. A fixture compiled by the old producer cannot validate this repair.
- Compiler/core checks and both-backend native qualification remain pending.
  Packed-byte pop representation is a separate previously documented concern.
