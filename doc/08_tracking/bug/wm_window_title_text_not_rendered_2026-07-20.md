# WM window titlebar title text never renders in-guest (close X, taskbar labels, clock all render)

- **ID:** wm_window_title_text_not_rendered_2026-07-20
- **Status:** OPEN
- **Severity:** medium (visual completeness; only n=1 window observable on diskless boots)
- **Found by:** GUI-CHECK surface lane, 2026-07-20

## Evidence
On the current evidence boots (desktop-ready, 0 exceptions, glyphs working):
full-frame text-primary pixel census = close "X" glyph (14 px at x=2063-2067,
inside the 20x20 close rect) + taskbar labels (178 px) + taskbar clock
(312 px) ≈ all 512 measured text pixels. The "System Console" window's
title (drawn at window.x+66, titlebar y-band) contributes ZERO pixels —
scanning x480-2080 y320-348 finds only titlebar fill, gems, close rect,
and the X. Prior session notes attributing "titlebar text" to earlier
pixel counts were actually counting the X glyph.

## Why it is interesting
Close X, taskbar labels, and the clock all render through backend text
calls; the title call on the same chrome path does not. Prime suspects:
- the title-fit width math (`max_chars = (width-92)/8`-style guards) or the
  text_fit slice path behaving differently for multi-char dynamic text;
- title string integrity in-guest (window.title flows through
  struct/channel paths where documented boxing landmines live — cf.
  for_loop_over_text / tag-shift family), while "X" is a literal;
- draw order/clipping specific to the title (drawn after fills, but a
  clip/scissor or gradient interplay could differ).

## Repro
Boot the desktop evidence harness (diskless), screendump, scan the
titlebar band for dark pixels excluding the close-rect area. n=1 window on
diskless boots (ensure_baremetal_system_window "System Console").

## Fix direction
Gated probe on the live chrome title call: print title.len(), first bytes,
computed max_chars, and the backend draw entry — one boot names whether
the string, the fit math, or the draw is at fault; then fix at root with
the campaign's boring-construct recipes.
