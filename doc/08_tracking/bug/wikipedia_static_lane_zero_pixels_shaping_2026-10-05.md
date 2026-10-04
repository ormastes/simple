# wikipedia.org static lane returns 0 pixels; Arabic shaping costs ~45 s per run (2026-10-05)

Status: PARTLY FIXED (cost fixed in branch `work/browser-wiki-crash-fontcache`;
the 0-pixel frame is OPEN, owned by the font-fallback / Draw IR lane).

## "array index out of bounds: index is 0 but length is 0" is not an engine crash

The error came from the measuring harness, not the engine.
`render_html_to_pixel_array` returns `[]` for wikipedia.org. The harness then
indexed that empty array while hashing rows. A plain render does not crash.

## Why the static lane returns `[]`

`_simple_web_layout_render_html_engine2d_execution` on the saved page, at
800x600, cpu ("software") backend, budget disabled, reports:

    rendered=146 skipped=2 occluded=0
    reason=unsupported Draw IR commands skipped: text-font-shaping

Two text commands, the Arabic-script language links, are skipped by
`gc_async_mut/gpu/engine2d/draw_ir_adv.spl` (`if not font_ready: skipped += 1`).
Font resolution returns `reason=font-shaping-unavailable` for Arabic: the
shaped run is invalid, so the text has no usable advances.
`simple_web_layout_render_html_pixels_engine2d_at_time_with_animations_with_images`
(`simple_web_layout_engine2d_fast.spl`) then discards the WHOLE frame whenever
`skipped_command_count != 0`. The result is 0 pixels for a page where 146 of
148 commands rendered.

Unblock: make Arabic shaping succeed (font-fallback lane, #2503), or decide
whether a frame with a few unshapable runs is presentable (Draw IR/paint lane).
Both are outside the style/layout lane, so this is recorded and not changed.

## Cost: the face digest (fixed)

In `_resolve_selected_shaped_glyph_run`, every complex-script run called
`shaper_with_ot_face`. That hashes the whole face blob with pure-Simple
SHA-256. For the 845 KB Arabic face this took 45–48 s per run in the
interpreter.

Fix: `shaper_face_blob_sha256_hex_cached` + `shaper_with_ot_face_blob_hex`
(`skia/feature/shaper/shaper.spl`). The digest is memoised per
(path, length, native face identity) and the identity check is unchanged.
Measured (interpreter): a second Arabic run went from 52.8 s to 0.57 s.
wikipedia.org static render went from 398 s to 211 s. On example.com,
news.ycombinator.com, google.com, a 52 KB article and wikipedia, the main and
software lanes are pixel-identical to main, row for row.

The first Arabic run still pays the hash once per process. The native
`rt_sha256_*` externs give correct digests in the interpreter but WRONG
digests under the JIT (`rt_sha256_write(h, data, len)` hashes the wrong bytes;
`"abc"` -> `736722f2...` instead of `ba7816bf...`), so they cannot be used
yet. That is a seed JIT extern ABI defect, open.

Specs: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_style_jit_identity_spec.spl`
does not cover this. The pixel A/B in the PR body is the evidence.
