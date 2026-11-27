# A float's authored fractional height is dropped; a `clear` sibling starts high (2026-11-28)

Status: open (unowned)
Owner lane: web render parity (float layout)
Oracle: Chrome for Testing 159.0.8154.6 aarch64, `--headless=new --disable-gpu
--hide-scrollbars --force-device-scale-factor=4`, window 400 CSS px wide.

## Defect

A float with an authored fractional `height` is laid out and painted at its
whole-px height, and a following `clear: both` block starts at that whole-px
bottom.

Fixture (inside a 50px block whose top is CSS y 350):

    <div style="float:left;width:100px;height:10.75px;background:#aa5500"></div>
    <div style="clear:both;height:5px;background:#bb6600"></div>

| k | what | Chrome rows | Simple rows |
|---|------|-------------|-------------|
| 4 | float box | 1400..1442 | 1400..1439 |
| 4 | `clear:both` sibling | 1443..1462 | starts at 1440 |
| 1 | float box | 350..360 | not measured |
| 1 | `clear:both` sibling | 361..365 | not measured |

The gap is on base `d40623d3f59` and is unchanged by the in-flow fix below.

## Why the in-flow fix does not cover it

`block_after_fractional_height_chrome159_spec` fixed the in-flow case: the
block return in `simple_web_html_layout_renderer_layout_engine.spl` adds
`authored_height_frac_milli` to the end residual and the parent's block cursor
carries it. A float does not advance the block cursor; its bottom lives in the
float context (`float_ctx_*`, whole CSS px) and clearance reads it from there,
so the fraction is lost before the cleared sibling is placed. The float's own
box also gets no device extra height.

## Suggested fix

Keep the float's bottom in milli CSS px in the float context (or a parallel
residual), let clearance hand the residual to the cursor (`cy_frac`), and record
the float box's device extra height as the in-flow path does.
