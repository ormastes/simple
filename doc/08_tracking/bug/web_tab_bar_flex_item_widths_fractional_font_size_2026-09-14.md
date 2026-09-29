# tab-bar flex items are 1-2 px narrow — fractional UA font-size, not flex (2026-09-14)

Status: **OPEN** — characterised, not fixed. Round 15 confirmed it is NOT the
flex distribution formula the round-14 metrics doc suspected.

## What the differ says

`tab-bar` is the one catalog page whose signature is horizontal: 7 of 7 root
mismatches are `flex-item`, every `dy` and `dh` is 0, every `dw` is wrong.

| key | Chrome w | dw | dx |
|---|---|---|---|
| path:0/0/0 | 74 | 2 | 0 |
| path:0/0/1 | 54 | 1 | 2 |
| path:0/0/2 | 89 | 2 | 3 |
| path:0/0/3 | 80 | 2 | 5 |
| path:0/0/4 | 108 | 2 | 7 |
| path:0/0/5 | 77 | 1 | 9 |
| path:0/0/6 | 73 | 2 | 10 |

`dx` is the running sum of the `dw`s before it — i.e. there is ONE error,
repeated per item, and the x drift is entirely inherited from it.

## Why it is not a flex formula

The buttons are content-sized: Chrome reports no `flex-basis`/`flex-grow`
override on them, `parent-display=flex`, `flex-direction=row`,
`flex-wrap=nowrap`. A wrong `flex-basis: auto` vs `0%` reading, or a wrong
free-space distribution, would produce errors proportional to the item count or
to the free space — not a flat 1-2 px per item that is independent of the
item's own width (74 and 108 are both off by 2; 54 and 77 are both off by 1).

The discriminating measurement is the computed font size Chrome reports on
those buttons:

```
font-size=13.3333px
```

That is the UA form-control size (`13.3333px`, not 13). A layout engine that
truncates or rounds it to an integer before measuring text advances loses
~0.33/16 of every glyph's width, which over a 5-10 character label is exactly
the observed 1-2 px, and does not scale with the box.

## Where to look

`FORM_CONTROL_UA_FONT_SIZE_PX` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`,
and `Style.font_size` (an `i32`) — the whole style record carries font size as
integer px, so this is not a one-line constant change but a question about
sub-pixel font sizes in the style model. Do not "fix" it by nudging the
constant: that would trade this page's error for every other page's.

## Not to be confused with

`doc/08_tracking/bug/web_layout_vertical_drift_accumulates_16px_per_construct_2026-09-14.md`
(fixed round 15) — that was vertical and touched `html` only. `tab-bar`'s 7/7
did not move under it, as expected.
