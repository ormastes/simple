# Native `Const` pattern lowers irrefutably

**Status (2026-07-15):** source fixed; focused Rust regressions added but not
executed in the source-only lane.

## Symptom

In a native SimpleOS compiler, a `MirInstKind.Const(dest, _, _)` match arm accepted non-`Const` values and treated the enum header as `LocalId`. The filesystem compiler faulted in `var_reassign_local_id_value` after MIR lowering.

## Evidence

The failing ELF omitted a `Const` discriminator check and loaded word zero from the enum object. A guarded implementation that first compares `rt_enum_discriminant` numerically emits `rt_enum_payload`, `rt_index_get(0)`, then the `LocalId` accessor and advances past this fault.

## Required fix

Fix native pattern lowering for keyword-named, multi-field enum variants. Add a target-code regression proving a standalone first `Const` arm checks its discriminator and extracts payload fields. Then remove the allocation-heavy marker workaround in `var_reassign_analysis.spl` and measure warm optimizer latency/RSS.

## Resolution (2026-07-15)

Expression and statement match lowering now give a variant owned by the
subject enum precedence over an unrelated same-named struct. The focused tests
`test_subject_enum_const_variant_beats_unrelated_const_struct` and
`test_standalone_match_subject_enum_const_variant_beats_unrelated_const_struct`
require both the discriminator check and payload extraction.

The temporary `MirInstKind.Const` marker plus `rt_enum_discriminant` workaround
was reverted before this fix and is absent from the current
`var_reassign_analysis.spl`; therefore there is no retained marker allocation
or optimizer performance delta to remove or measure. Executing the focused
tests remains the only closure evidence still pending.
