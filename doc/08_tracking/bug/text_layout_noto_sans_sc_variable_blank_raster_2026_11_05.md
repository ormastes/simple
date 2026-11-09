

Round 15 update: spec test/01_unit/lib/nogc_sync_mut/text_layout/noto_sans_sc_atlas_ink_spec.spl (Han glyph staged at 16px leaves non-zero atlas alpha) passes on the stock seed AND on a seed with the new rt_font_glyph_bitmap_index/advance_index interpreter bridges, so the blank atlas is NOT reproduced in the interpreter; the bridges close a real gap (shaped-run index path had no interpreter backing) but are not shown to be the cause. Remaining suspect: native/GPU atlas upload. Needs a native run on the 2026-11-05 browser_renderer lane.


2026-11-09 p3 scoping (release/1.0.0 @438457b0775, isolated worktree, seed bootstrap binary, aarch64 host):
- Both repro specs PASS interpreted: noto_sans_sc_variable_raster_ink_spec 1/1 (rt_font_glyph_bitmap ink>0 for U+0041 and U+4E2D at 16px) and noto_sans_sc_atlas_ink_spec 1/1 (FontRenderer shaped path: staged Han glyph quad covers non-zero atlas alpha). --mode=native degrades to interpreter on the seed (no MC/DC probes; unrelated simple_contract_check JIT crash).
- Asset ruled out: 17,772,300 bytes, sha256 a3041811...f0da matches the staged Draw IR identity, fvar present at offset 156.
- Confirmed adjacent defect: src/runtime/runtime_font.c uses stb_truetype, which has no variable-font instancing — axes=wght=100 is silently ignored (default master rasterized; wrong weight, never transparent).
- f6dc86d1af5 (2026-11-07) closed the real seed-interpreter glyph-index bridge gap (rt_font_glyph_bitmap_index/rt_font_glyph_advance_index) but per the round-15 note the atlas spec passed even on the stock pre-bridge seed, so that gap is not the proven cause of the 2026-11-05 blank atlas.
- Conclusion: the original symptom (selected=true ok=true nonwhite=0) is not reproducible at the FontRenderer/runtime-font layer in the interpreter. Remaining suspect: native/GPU atlas-upload lane of the Engine2D draw-ir fast path. Verification requires the pure-Simple self-hosted bin/simple (not built on this host) or the browser_renderer GPU lane. No source fix attempted; bug_db row kept open with diagnosis.
