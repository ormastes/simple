# Arabic OpenType shaping never ran: validator, GDEF tag, GPOS defects (2026-10-05)

Status: fixed on `work/ot-validator-arabic`.

Wikipedia's Arabic language link fell back to unshaped glyphs: the canonical
GSUB/GPOS transaction for Noto Sans Arabic was rejected or produced wrong
positions. Six independent defects:

1. **Validator rejected legal fonts.** `ot_parser_layout.spl` bounded each
   Script/LangSys/Feature/Lookup/subtable by its nearest sibling offset and
   rejected repeated offsets. OpenType allows any order and shared subtables.
   It now bounds every read by the parent table end, keeps fixed depth, u16
   loops, and the shared work budget (`_subtable_reach_end`).
2. **GDEF tag typo.** `1195656006` ('GDCF') was used instead of `1195656518`
   ('GDEF') in `ot_layout_context.spl`, `ot_layout_gpos_data.spl`,
   `ot_parser_layout.spl`. GDEF was never found in real fonts, so every
   IgnoreMarks lookup failed. The skia specs encoded the typo; fixed there too.
3. **GPOS type 1 (single adjustment) unsupported** — Noto's chained mark
   positioning nests it. Implemented in `ot_layout_gpos.spl`.
4. **ValueRecord device/variation offsets rejected, PairPos format 1 base
   wrong.** Values now go through `gpos_data_value_adjusted` at default
   coordinates; format 1 device offsets are relative to the PairSet.
5. **`_add` was a no-op in the interpreter.** It mutated a class parameter,
   which the interpreter binds by copy, so pair kerning and single adjustments
   vanished. It now writes through `records[index]`.
6. **RTL mark offsets used the LTR pen rule.** `gpos_apply_directed(..., rtl)`
   adds back the advances after the base, as HarfBuzz does for backward runs.
   Arabic GPOS features are also no longer gated by source codepoint, so the
   dot glyphs produced by GSUB decomposition are positioned.

Oracle: CoreText at the font default instance (wght 400) — `العربية`, `فارسی`
and `بِسم` match glyph ids, advances and mark offsets exactly. Rendered
link vs CoreText: same ink bbox width (1..97 px at 40px), 2px baseline shift
from line layout.

Specs:
- reproducing: `test/01_unit/lib/skia/ot_layout_arabic_shaping_spec.spl`
  ("validates and shapes Noto Sans Arabic GSUB and GPOS").
- generalization: same file — shared lookup/subtable offsets accepted, a
  subtable past the table end rejected, a mutual ContextPos cycle rejected,
  and two further Arabic runs (Persian, harakat).

## Open: per-run validation cost (perf todo)

Each Arabic run re-selects plans, re-parses both catalogs and re-validates
every active lookup (`resolve_canonical_layout_run`, `ot_layout_shaper.spl`);
GPOS validation also runs twice (resolver, then inside `gpos_apply_directed`).
Measured ~15 s per run under the interpreter on a loaded host (load 25),
identical for the 1st and 3rd call — nothing is cached. Before this change the
same runs were rejected cheaply. Unblock: cache plan + catalogs + structural
validity per face content identity (the shaper's face digest), script,
language and feature list; keep the record-dependent dry run per call.
