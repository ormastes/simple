# Spreadsheet ASCII width builder owner import

Status: OPEN (P1). GitHub: https://github.com/ormastes/simple/issues/3314

V7 attempt `77c30a66569b4bde` records two HIR errors for source index 1100:
`module common.string_builder has no exported item RtStringBuilder` and unresolved
`RtStringBuilder` at line 13 of `src/app/office/sheets/ascii_width.spl`.

The short alias selects `src/app/common/string_builder.spl`, which declares only
`StringBuilder`. The required runtime builder belongs to `src/lib/common/string_builder.spl:62`.
Change the import to `use std.common.string_builder.{RtStringBuilder}`.
Driver and HIR owner normalization maps std to lib; existing app imports use this spelling.
No resolver fallback or owner checks change. Public ASC/JIS signatures and conversion
logic remain unchanged.

Independent source review: ACCEPT SOURCE ONLY. The accompanying
`test/01_unit/compiler/hir/string_builder_owner_collision_spec.spl` loads both physical providers and checks successful qualified import plus
rejection of the original ambiguous import. Regression AUTHORED, NOT EXECUTED.
Actual regenerated HIR/MIR/object generation, fresh native generation and Unicode/NUL
runtime acceptance remain PENDING. This document claims no native or runtime PASS.

Initial source binding: `3fc904b31db05ca6b3d6d60528eb1b60dc770dc9`.
Metadata integration parent: `cbf3d3facb5818c7d725ada4d8117674f5ce111a`.
