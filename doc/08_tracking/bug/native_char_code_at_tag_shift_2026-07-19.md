# Native codegen: text.char_code_at returns value >>3 (tag-shift corruption) on freestanding lane

- **ID:** native_char_code_at_tag_shift_2026-07-19
- **Status:** OPEN
- **Severity:** high (silent wrong value; broke all baremetal WM chrome text)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
In the SimpleOS desktop kernel, `"X:58".char_code_at(0)` returns **11**.
Expected 88 ('X'). 88 >> 3 == 11 exactly — the BoxInt <<3 tag-shift
signature (same family as the seed ANY-channel enum-handle mangling,
doc'd 2026-07-04), not random garbage.

Serial evidence (gated probe, 2026-07-19 boot):
```
[glyph-probe] slen=4 cc0=11
```
`len()` on the same literal is correct (4). `get_glyph_8x16(0x58u8)` with a
literal argument returns correct rows (glen=16 g4=108 g8=124), so the
corruption is exactly at the char_code_at call/return boundary.

## Impact
`SharedWmPixelBufferBackend._px_draw_text` (window_scene_draw_ir.spl) feeds
`char_code_at(ti) as u8` into the glyph table: every lookup misses its
branch, chrome text is wrong for all labels/titles/clock in-guest.
(Full text blankness additionally involves the u8 `!=` bit-test suspect —
tracked separately once probe-confirmed.)

## Repro
Gated `_probe_debug()` serial probe in gui_entry_desktop.spl; seed
native-build to x86_64-unknown-none; boot -kernel or OVMF; grep serial for
`glyph-probe`. Hosted lane (seed interpreter) returns the correct 88 —
freestanding-native only.

## Fix direction
Audit native-lane text method returns for missing untag/unbox on the
char_code_at path (value appears to be handed back still-tagged, then
consumed as if raw, i.e. one >>3 applied to the payload). Workaround in
callers: use a byte accessor where ASCII suffices.
