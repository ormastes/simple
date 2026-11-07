

Round 15 update: spec test/01_unit/lib/nogc_sync_mut/text_layout/noto_sans_sc_atlas_ink_spec.spl (Han glyph staged at 16px leaves non-zero atlas alpha) passes on the stock seed AND on a seed with the new rt_font_glyph_bitmap_index/advance_index interpreter bridges, so the blank atlas is NOT reproduced in the interpreter; the bridges close a real gap (shaped-run index path had no interpreter backing) but are not shown to be the cause. Remaining suspect: native/GPU atlas upload. Needs a native run on the 2026-11-05 browser_renderer lane.
