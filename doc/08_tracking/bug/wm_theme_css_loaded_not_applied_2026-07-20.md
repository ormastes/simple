# Guest CSS theme loads (bytes=1276 loaded=1) but chrome colors never change

- **ID:** wm_theme_css_loaded_not_applied_2026-07-20
- **Status:** OPEN
- **Severity:** medium (CSS-file theming works host-side end-to-end; in-guest the load rung is proven but application is dead)
- **Found by:** GRADIENT-DRAWIR lane Boot B, 2026-07-20

## Evidence
Boot B (OVMF, fat32-theme.img carrying the slate_dark palette
`#0f172a`/`#1e293b`/`#2050a0` as /THEME.CSS): serial prints
`[desktop-gui] theme bytes=1276 loaded=1` — the VFS allowlist fix works,
the file is read, `wm_chrome_colors_from_css_text` is invoked and
`register_wm_chrome_theme` is called before the first frame. Yet the
rendered frame is byte-identical to Boot A in all three probe regions:
desktop `#5a7fb5`, body `#182230`, titlebar `#dceafb` — pure Aqua defaults.
0 exceptions, desktop-ready, clock-region sha unchanged.

## Suspects (in likelihood order)
1. `wm_chrome_colors_from_css_text` (src/lib/common/ui/wm_theme_css.spl)
   parse returning defaults in-guest — the byte-scan parser is host-proven
   but may hit a freestanding text/bytes landmine (e.g. the documented
   char_at-on-dynamic-strings class) and silently fall back.
2. `register_wm_chrome_theme` / `_wm_chrome_override` staleness: consumers
   may have already snapshotted `wm_chrome_theme()` values (module-init or
   first-call caching) before registration, so the override never reaches
   the draw path.
3. The live chrome path (`_wm_draw_ir_window_batch`) reading theme fields
   through a path that bypasses the override hook entirely.

## Repro / next probe
One gated serial probe in-guest: print (a) parsed token count + first parsed
color from `wm_chrome_colors_from_css_text`, (b) `wm_chrome_theme().desktop_bg`
AFTER registration, (c) the desktop_bg value the compositor actually uses at
first frame. Whichever link disagrees names the fix. Host-side control: the
same CSS text through the same fns flips all 6 slots (proven 9351608392d).

## Note
The guest wiring source in gui_entry_desktop.spl was lost to a parallel-
session WC clobber after the evidence ELF was built; it must be re-applied
(reconstruction + rebuild + one boot) before this bug's probe can run.
