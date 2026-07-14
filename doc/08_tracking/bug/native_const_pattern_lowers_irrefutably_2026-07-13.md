# Native `Const` pattern lowers irrefutably

## Symptom

In a native SimpleOS compiler, a `MirInstKind.Const(dest, _, _)` match arm accepted non-`Const` values and treated the enum header as `LocalId`. The filesystem compiler faulted in `var_reassign_local_id_value` after MIR lowering.

## Evidence

The failing ELF omitted a `Const` discriminator check and loaded word zero from the enum object. A guarded implementation that first compares `rt_enum_discriminant` numerically emits `rt_enum_payload`, `rt_index_get(0)`, then the `LocalId` accessor and advances past this fault.

## Required fix

Fix native pattern lowering for keyword-named, multi-field enum variants. Add a target-code regression proving a standalone first `Const` arm checks its discriminator and extracts payload fields. Then remove the allocation-heavy marker workaround in `var_reassign_analysis.spl` and measure warm optimizer latency/RSS.
