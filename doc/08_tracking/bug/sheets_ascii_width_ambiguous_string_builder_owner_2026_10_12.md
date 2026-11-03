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

**Revalidated 2026-11-02: still plausible because OPEN (P1). GitHub: https://github.com/ormastes/simple/issues/3314; no merged fix commit with a passing regression is cited in this doc.**

## Source reconciliation — 2026-11-03

Source repair is already present; execution verification remains pending.
At release snapshot `d591d1df36f4bad9692c8eeab65c1a3a7ba69e6e`, the actual
`src/app/office/sheets/ascii_width.spl` imports
`std.common.string_builder.{RtStringBuilder}`. The owning change is
`5ef5ec6879d8aa0cd4dff214ef73e1f14bdc9f87`
(`fix(office): resolve ASCII width builder through std namespace`), reachable
in the release history. Its supporting report is
`doc/08_tracking/bug/ascii_width_rt_string_builder_namespace_2026_10_13.md`.
This supersedes any inference from the previous revalidation that the source
import has not been repaired. It does not supply a passing regression receipt.

The existing regression set already distinguishes the required owner from an
ambiguous app alias and exercises the public conversion functions:

- `test/01_unit/compiler/hir/string_builder_owner_collision_spec.spl`:
  both provider surfaces are loaded; the qualified library import resolves;
  the app alias is rejected when its provider lacks `RtStringBuilder`.
- `test/01_unit/app/office/sheets/ascii_width_spec.spl`: actual ASC/JIS
  entrypoints, full-width letters/digits/space, CJK, supplementary characters,
  embedded NUL, and empty input.
- `test/01_unit/app/office/sheets/ascii_width_long_spec.spl`: long ASCII and
  mixed Unicode/NUL conversions through the same public entrypoints.

No duplicate implementation fix or tests were added in this reconciliation.
No admitted source-matched compiler/test runtime was available to this worker;
no independent compiler rebuild, seed fallback, native test or source-load-only
test was run. Status remains **AUTHORED_UNRUN / verification pending**. The
canonical bug database is unchanged; this report does not close its open row.

Remaining acceptance: execute all three existing specs through the admitted
native runner, retain actual case counts and producer/source/artifact hashes,
and qualify regenerated HIR/MIR/object generation for the Sheets owner. The
original ambiguous-owner failure must be distinguished from any new compiler
or runtime blocker. Import text alone is not runtime verification or TDD GREEN.
