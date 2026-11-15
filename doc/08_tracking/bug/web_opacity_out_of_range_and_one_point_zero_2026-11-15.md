# `opacity: 1.0` paints the element fully transparent; out-of-range opacity is not clamped (2026-11-15)

Status: OPEN. Severity: high for Simple web paint — `opacity: 1.0` is a common
authored value and makes the element invisible.

## Defect

`parse_opacity_pct` (`browser_engine/simple_web_html_layout_renderer_foundation.spl`,
`fn parse_opacity_pct`) reads only the fractional digits of any value that
contains a `.`, ignoring the integer part, and reads an integer with
`parse_int`, which skips the minus sign and is never clamped above 1 for a
unitless number. CSS Color 4 section 11.2: `opacity` is a `<number>` or
`<percentage>` clamped to [0, 1] at computed-value time.

Both declaration paths (the O(k) dispatch table and the full-probe
`_apply_decls_without_grid`, `decl_apply.spl` `opacity_decl`) call it, so the
wrong value reaches `Style.opacity_pct` either way.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, built 2026-11-14, interpreter)

```
apply_decls(renderer_default_style(), "opacity:" + v, 16).opacity_pct
apply_decls(renderer_default_style(), "opacity:" + v + ";letter-spacing:0px", 16).opacity_pct
parse_opacity_pct(v)
```

All three give the same `actual`. Chrome 159.0.8154.6 headless shell,
`getComputedStyle(d).opacity` after `d.style.opacity = v`:

| value | Chrome computed | expected `opacity_pct` | actual |
|---|---|---:|---:|
| `1.0` | 1 | 100 | **0** |
| `1.5` | 1 | 100 | **50** |
| `2` | 1 | 100 | **2** |
| `-1` | 0 | 0 | **1** |
| `-0.5` | 0 | 0 | **50** |
| `0.5` | 0.5 | 50 | 50 |
| `150%` | 1 | 100 | 100 |

## Fix direction

Parse the integer part before the `.`, honour a leading `-`, and clamp the
result to 0..100 for both the number and the percentage form. The
`style_property_id_parse_opacity_pct` typed parser (`style_property_id.spl`)
has a separate integer-part path and should be checked against the same table.

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_style_value_parsers_spec.spl`
pins only the in-range rows (`0`, `1`, `0.5`, `.25`, `50%`, `150%`); the
wrong rows above are kept out of the spec until the fix lands.

Re-verified still OPEN 2026-11-15 at `ba2663afde6` (after the upstream border/abspos/whitespace fixes): every row above reproduces unchanged.
