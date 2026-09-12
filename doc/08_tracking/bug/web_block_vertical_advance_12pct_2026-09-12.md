# Block vertical advance over-measured ~12 % — cause still NOT isolated (2026-09-12)

**Status:** OPEN. Not fixed. Four candidate causes now excluded by fixture.
**Component:** pure-Simple web renderer, block layout.

## Symptom

On the shared catalog, blocks accumulate ~12 % more vertical advance than Chrome:
the overview card ends at y=**414** vs Chrome's 371 (+43 px over the card), and
the tab-bar strip occupies y=24..**88** vs 24..76 (+12 px).
Source: `doc/10_metrics/ui/chrome_vs_simple_catalog_diff_macos_2026-09-12.md`, rank 4.

## Excluded causes

| candidate | control | verdict |
|---|---|---|
| explicit `line-height` | `font:16px/1.5` paragraph occupies 23 px ≈ 24 | correct (prior diagnosis) |
| adjacent-sibling margin collapsing | two `<p>` leave a 16 px gap = 1em, not 32 | collapses correctly (prior diagnosis) |
| **plain block advance** | two stacked `margin:0; height:100px` `<div>`s | **exact**: red y=0..99, blue y=100..199 |
| **default `line-height: normal`** | `<p style="margin:0;font-size:16px">` | **18 px**, matching Chrome's `normal` ≈ 18-19 px for a 16px system font |

The last two are new here and are the two the earlier diagnosis explicitly left
open. They are both clean, so the 12 % does **not** come from the block advance
rule itself, nor from the default line box height.

## Fixture (reproduces the controls above)

```html
<html><body style="margin:0;padding:0;background:#ffffff">
<div style="margin:0;width:200px;height:100px;background:#ff0000"></div>
<div style="margin:0;width:200px;height:100px;background:#0000ff"></div>
<p style="margin:0;font-size:16px;background:#00ff00">Hello world</p>
<div style="margin:0;width:200px;height:20px;background:#ffff00"></div>
</body></html>
```

Rendered at 300x300 with
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_2D_BACKEND=cpu_simd
build/cargo-r2/release/simple run examples/06_io/ui/web_render_page_ppm.spl`,
column x=5 run lengths:

```
y   0..99  (100 px) (255,0,0)
y 100..199 (100 px) (0,0,255)
y 200..217 ( 18 px) green paragraph box
y 218..237 ( 20 px) (255,255,0)
```

## Where to look next

Remaining candidates, in the order the evidence now favours:

1. **UA default box sizes for `h1` / `h2` / `blockquote` / `button` / list items** —
   the catalog is heading- and list-heavy and the plain-div and plain-`<p>`
   controls are both clean, so a per-element-type UA default is the strongest
   remaining hypothesis.
2. Padding/border contribution on the specific catalog card classes.
3. Multi-line wrapping: the controls above are all single-line.

Chrome's exact box geometry without pixel-reading: `--headless=new --dump-dom`
executes scripts, so a fixture whose `<script>` writes each block's
`getBoundingClientRect().bottom` into a `<pre>` yields Chrome's edges directly in
the dumped DOM. That is the cheapest next step and was not run here.

## Why no fix landed

The brief allowed a fix only if it were ≤ 30 lines at a named `file:line`. No
file:line could be named: every fixture that isolates a single mechanism is
correct, so the cause is a composition of element-specific defaults that needs
the per-element-type sweep above before a line can be attributed. Guessing a
line would be worse than filing.
