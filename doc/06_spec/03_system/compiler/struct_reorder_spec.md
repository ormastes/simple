# Struct field reorder through the production layout API

Executable: `test/03_system/compiler/struct_reorder_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`.

Status: **Phase 1 diagnostic PASS: 11 passed, 0 failed, 2273 ms; exit 0**.
Retained evidence under `build/phase-one-storage-gui-diagnostic/`:
`struct_reorder_spec/cycle-one.log`, adjacent `cycle-one.rss.env`,
`cycle-one.exit`, and `cycle-one.command.sdn`; source/input identities are in
`layout-baseline-inputs.sdn`. The complete eleven-scenario canonical spec ran
once for this baseline. No already-passing scenario was rerun.

This manually maintained guide is not generated docgen output. Native execution,
Rust/Simple behavioral parity, and docgen remain unverified; the focused Phase 1
result does not qualify the whole suite or a release product.

The public `compiler.types.type_layout` API dispatches to `layout_core.spl` and
`arch_and_verify.spl`. Eleven scenarios replace stale source-substring probes:

1. Sort mixed-size HIR fields descending; preserve symbol/visibility metadata
   and leave the declaration input unchanged.
2. Preserve declaration order within equal-size integer/boolean groups.
3. Default Simple layout: order wide/word/half/byte, offsets 0/8/12/14,
   total size 16 and alignment 8.
4. Simple preserve_order: declaration order byte/wide/half/word,
   offsets 0/8/16/20, size 24 and alignment 8.
5. C layout: preserve that declaration order even when Simple-only flags would
   request packing or permit reordering.
6. Simple compactq: reordered fields, size 15, alignment and field alignments 1.
7. Simple compactq plus preserve_order: declaration-order offsets 0/1/9/11,
   size 15 and alignment 1.
8. Architecture-aware reorder: a pointer preceding a u64 moves behind it on
   X86, but retains its equal-size declaration-order tie on X86_64.
9. Architecture-aware layout: the pointer/u64/byte fixture has X86 offsets
   0/8/12 in wide/pointer/byte order, size 16/alignment 4; X86_64 has
   pointer/wide/byte offsets 0/8/16, size 24/alignment 8.
10. Empty reorder and default, target-aware, and packed layouts remain empty,
    size/stride zero and alignment one.
11. A singleton u16 retains identity and offset zero; natural alignment is two,
    explicitly packed alignment is one, with size/stride two in both cases.

Every layout oracle checks exact field count before indexing, then field names,
offsets, sizes, alignments, total size, alignment, and stride. HIR fixtures supply
all current field members, including visibility. No filesystem contents or
implementation-token checks are used. Coverage annotations declare 80% targets
for both actual split owners; no measured coverage is claimed.

The legacy `test/system/struct_reorder_spec.spl` duplicate is removed after
preserving its Simple layout intent in real computation assertions. Its Rust
seed source-token probes never established behavior: actual Rust/Simple parity
remains an explicit separate qualification gap. No claim is made for parser
integration, generated native field accesses, target ABI execution, or emitted
C/Rust compatibility. The hand-built HIR exercises the real layout owner, not
the parser or a native compiler pipeline.
