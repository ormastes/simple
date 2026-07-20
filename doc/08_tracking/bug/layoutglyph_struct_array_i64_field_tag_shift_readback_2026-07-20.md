# LayoutGlyph struct-in-array i64 fields read back tag-shifted on the freestanding native lane — zero glyph quads, no text on SimpleOS desktop

- **ID:** layoutglyph_struct_array_i64_field_tag_shift_readback_2026-07-20
- **Status:** WORKED AROUND per-site (scalar mirrors in `_prepare_text_active`); root compiler codegen bug OPEN
- **Severity:** P1 — silently killed ALL glyph text on the SimpleOS x86_64 desktop (taskbar clock, window titles, taskbar labels); no crash, no diagnostic
- **Lane:** native-build (Rust seed frontend, cranelift, `--entry-closure`, x86_64-unknown-none), OVMF/GRUB multiboot boot
- **Class:** the documented "BoxInt <<3 / tag-shifted views of one boxed integer" codegen family (see GLYPH-FIX-3 retraction note in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` and `baremetal_option_field_unwrap_faults_class_2026-07-18.md` for siblings)

## Symptom

At origin/main tip (base 9fdeaee2314, 2026-07-20) the SimpleOS desktop
(`gui_entry_desktop.spl`) boots to `desktop-ready` with a 99.83%-coverage
frame but renders ZERO glyph ink anywhere: no window title, no taskbar
labels, no taskbar clock (`clock_region_ink_pixels=0`, kernel logs
`[font-evidence-unavailable] reason=canonical-taskbar-clock-oracle-pending`).
The aqua-glyph OVMF gate honestly fails on the clock-ink oracle.

## Probe evidence (gated boot probes, OVMF boot, 2026-07-20)

The glyph pipeline is healthy right up to the quad producer:

```
[e2d-text-probe]  ir kind=plain len=11                                # draw-ir text cmd, text present
[vec-text-probe]  draw_text-entry text_len=11 has_sffi_ttf=1          # engine entry, text present
[vec-glyph-probe] prepare-entry content_len=11 font_size=12           # renderer entry, text present
[vec-glyph-probe] gwc-pre-insert cp=83 w=5 h=12 adv=6 plen=60         # rasterizer: REAL glyph bitmap
[vec-glyph-probe] active-after-layout_text layout_len=0 ...           # rast.layout_text: empty -> fallback loop
```

The fallback loop pushes correct values into `layout: [LayoutGlyph]`
(cp=83 'S', w=5 h=12). Reading the SAME entry back in the quad loop:

```
[vec-glyph-probe] quadloop-after-reget i=0 cp=0 w=0 h=0 face_id=0 face_gen=0 glyph_index=2305843009213693951
[vec-atlas-probe] producer-empty n_quads=0 overflow=0 content_len=11
```

- `cp=0` — the pushed `codepoint.to_i64()` (83) reads back as the `&7`
  tag-view (83<<3=664; 664&7=0), the exact three-shifted-views signature
  documented in the GLYPH-FIX-3 note.
- `glyph_index=2305843009213693951` (0x1FFFFFFFFFFFFFFF) — nil sentinel.
- Every draw therefore produces `n_quads=0` (with `valid=true`, since the
  batch construction itself succeeds), `_draw_font_batch_plan` "succeeds"
  with nothing to blit, and the draw-ir layer counts the command as
  rendered — a silent no-op.

## Regression window

The GLYPH-FIX campaign (2026-07-19) had this exact path producing
`n_quads=1..13` with real atlas coverage (see
`font_render_batch_transform_identity_default_not_applied_2026-07-19.md`
Evidence section) — the LayoutGlyph round-trip worked then. At tip it is
corrupt. Prime suspect (UNVERIFIED — not bisected): `f33dc52320f`
"fix(runtime): heap-box f64 on the native-build path (lossless container
floats)" changed container value boxing in the same window. A bisect boot
of `gui_entry_desktop` at `f33dc52320f^` vs `f33dc52320f` would confirm.

## Per-site workaround (landed with this doc)

`_prepare_text_active` (`font_renderer.spl`): scalar mirror arrays
(`fallback_cps: [i32]`, `fallback_xs: [i64]`) are filled alongside the
fallback `layout.push(LayoutGlyph(...))` and preferred over re-reading the
LayoutGlyph fields in the quad loop. Scalar primitive arrays round-trip
correctly on this lane (long-proven by e.g. the PMM refcount `[u16]`).
`FontRenderQuad`-in-array reads back correctly (consumer probes show real
`first_w/first_h/first_cov_nz`), so only the LayoutGlyph hop needed the
mirror.

**Also affected, NOT yet fixed:** `render_text_payload`
(`font_renderer.spl:~897`) has the identical fallback-then-reread pattern
and presumably the same corruption; it is not on the taskbar-clock path
and was left unchanged to keep this change minimal.

## Residual after the workaround (separate, smaller defect)

With quads restored, the desktop renders the taskbar clock digits
("00:00", 328 ink pixels in the clock crop vs 312 in the Jul-19 canonical)
and most label text, but SOME codepoints render as the 8x16 notdef box
(observed: 'H'/'W' in "Hello World", 'm' in "Terminal") — i.e. specific
re-get lookups return the notdef glyph instead of the cached real glyph.
Suspected: the glyph CACHE entry round-trip (another struct-in-container
hop; `gwc-entry ... cache_rcfg_id_len=0` also shows the cache's
render-config identity string reads empty) — same codegen family. Not
chased further in this change; the taskbar-clock oracle (digits) renders
correctly and deterministically.

## Root-fix direction

Fix the tag-shift on i64 struct-field round-trips through arrays in the
freestanding native codegen (boxing owner), then delete the scalar
mirrors. Bisect `f33dc52320f` first.
