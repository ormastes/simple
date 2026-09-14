# `<wbr>` is not a soft-break opportunity in the inline pen (2026-09-14)

Status: OPEN. Found in round 23 of the web↔Chrome layout-geometry parity arc,
while fixing `overflow-wrap: normal` (PR for
`doc/10_metrics/ui/web_chrome_parity_round23_2026-09-14.md`).

## Symptom

`<p style="width:80px">LongWord<wbr>BreakHere</p>` — the catalog's `html:wbr`
sample, `path:0/0/4/2/86/1/0` on `html.html`.

| | Chrome | Simple before round 23 | Simple after round 23 |
|---|---|---|---|
| `<p>` height | 48 (2 lines) | 216 (9 lines) | 24 (1 line) |

Round 23 removed the intra-word chopping that produced the nine lines, which is
a separate and now-fixed defect. What remains is the opposite error: Simple puts
both runs on ONE overflowing line because it has no break opportunity between
them, where Chrome breaks at the `<wbr>`.

## Why this is a different layer

The per-run wrapper (`_lay_compute_style_wrap_ranges_inner`) sees one text run
at a time and cannot know that a zero-width break opportunity sits between two
runs. The decision belongs to the inline pen in
`simple_web_html_layout_renderer_layout.spl` (the `in_inline_run` loop), which
already wraps ATOMIC inline boxes whole when they no longer fit the remainder of
the line — a `<wbr>`-preceded text run needs the same treatment.

## The discriminator is already measured

Measured against Chrome 152 `--headless=new --window-size=900,20000`, no author
CSS, 80 px box:

| markup | Chrome | Simple (post round 23) |
|---|---|---|
| `LongWord<wbr>BreakHere` | 36 (2 lines) | 18 (1 line) |
| `LongWord<i></i>BreakHere` | 18 (1 line) | 18 (1 line) |
| `LongWord<i>BreakHere</i>` | 18 (1 line) | 18 (1 line) |
| `Long<wbr>Break` | 18 | 18 |
| `LongWordX<wbr>BreakHere` | 36 | 32 |

The second and third rows are the control that matters: a run BOUNDARY alone is
correctly NOT a break opportunity in either engine. Only `<wbr>` is missing, so
the fix is scoped to that tag and must not widen to inline boundaries in
general.

Note `<wbr>` already has a rule elsewhere — `_simple_web_generates_no_box`
(`simple_web_html_layout_renderer.spl:229`) makes it boxless, matching Chrome's
0x0 rect. Being boxless and being a break opportunity are independent
properties; only the first is implemented.

## Cost of leaving it

Σ 24 on the one catalog row, plus the same 24 on `<ul>`, `<section>` and
`<body>` above it. It was +168 before round 23.
