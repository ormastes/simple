# Device-scale vertical placement: glyphs and media one device row low at k=4 (2026-11-24)

Status: open (fix in progress on `work/webrender-parity-vplace-20261124`)
Owner lane: web render parity (vplace)
Oracle: Chrome for Testing 159.0.8154.6 aarch64, `--headless=new --disable-gpu
--hide-scrollbars --force-device-scale-factor=4`, Liberation Sans.

## Defect A — a fractional-size gray glyph scales x only

`_glyph_outline` (`src/lib/common/encoding/sfnt_glyf.spl`) takes a fractional
size as `x_milli` and scales only the outline's x by `x_milli / size_px`. The
LCD path is right at 1x because its hint knots are built at the float size. The
gray path (above the 48 device px LCD cutoff) is unhinted, so its y stays at the
integer `size_px`.

At k=4, the 13.333px UA control font is 53.33 device px, but glyphs are drawn
53 px tall:

| 13.333px text, k=4 | Chrome ink rows / centroid y | Simple |
|---|---|---|
| `Simple` | 49-98 / 71.830 | 50-98 / 71.937 |
| `HHHHH` | 171-207 / 188.981 | 172-207 / 189.112 |

Ink mass is 0.5-1.3% low and the centroid is 0.11-0.14 row low. Integer sizes
(13px = 52, 14.5px = 58) match. 18.72px (74.88 -> 75) is off by too little to
show.

This is also why `#11157` kept the input value's `font-size-milli` at 1x only.
At k=4 the 53 px-tall glyph put `form_control_paint_chrome159_spec` AC-11's
first ink row at 46 against Chrome's 45.

## Defect B — line-placed atomic boxes drop the line's start fraction

An inline line that starts at a fractional cursor y lays its atomic boxes out
with `box_device_inline_dy_record`. Examples are canvas, svg, audio and video
after an `<h2>` with 19.92px margins: catalog animation, line top 95.84375.

That record is relative to the nearest cursor-placed ancestor. The line's own
residual (`cy_frac` minus the container's `origin_frac`) is never added. The
boxes therefore snap from the whole-px line top.

| catalog animation probes, k=4 | Chrome rows | Simple |
|---|---|---|
| `<svg width=120 height=40>` | 439-598 | 440-599 |

## Not covered here

- The audio control's `0:00 / 0:00` label is missing entirely.
- The animation 4x text lines sit 0.15-0.43 device px off in x.
- An svg's own viewport clip does not follow `device-y-offset`
  (`_dir_scale_command` scales `clip_rect` without the offset).
