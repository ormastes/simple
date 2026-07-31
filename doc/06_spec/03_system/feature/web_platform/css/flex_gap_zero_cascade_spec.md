# CSS flex gap zero cascade

> Static candidate manual — runtime unclaimed. This hand-reviewed mirror
> records expected oracles from the executable SSpec; it is not generated PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Fixture

```html
<style>
html,body{margin:0;width:12px;height:4px;background:#fff}
.row{display:flex;width:12px;height:2px;gap:4px}
.red{width:4px;height:2px;background:#dc2626}
.blue{width:4px;height:2px;background:#2563eb}
</style>
<div id="dispatch-row" class="row" style="gap:0">
  <div id="dispatch-red" class="red"></div>
  <div id="dispatch-blue" class="blue"></div>
</div>
<div id="full-row" class="row" style="gap:0;visibility:visible">
  <div id="full-red" class="red"></div>
  <div id="full-blue" class="blue"></div>
</div>
```

## Parse the split-cascade zero-gap fixture

Expected semantic row nodes are `div#dispatch-row` and `div#full-row`. The
composition source kind is expected to be `html_ast`.

## Resolve zero-gap Web layout geometry

Both rows are expected to expose `[gap_px,row_gap_px,column_gap_px]` as
`[0,0,0]`.

| Component | Expected box `[x,y,w,h]` |
|---|---|
| `dispatch-row` | `[0,0,12,2]` |
| `dispatch-red` | `[0,0,4,2]` |
| `dispatch-blue` | `[4,0,4,2]` |
| `full-row` | `[0,2,12,2]` |
| `full-red` | `[0,2,4,2]` |
| `full-blue` | `[4,2,4,2]` |

## Emit adjacent canonical Draw IR rectangles

The four colored items are expected to remain ordinary canonical `rect`
commands. Red commands use `0xFFDC2626`; blue commands use `0xFF2563EB`.
Their command geometry exactly matches the child boxes above, proving that no
private painter or backend-specific gap correction is involved.

## Render exact zero-gap Engine2D pixels

Expected skipped-command count: `0`.

Expected full 12-by-4 framebuffer (all 48 pixels):

```text
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
```

## Claim boundary

This scenario claims supported non-negative integer/px zero reset semantics
for Flex `gap` through the two canonical declaration paths. Percentage gaps,
multi-column `normal`, unsupported units, malformed/negative declarations, and
complete CSS Box Alignment parity remain outside this slice.

## Evidence provenance

No runtime, bootstrap, or docgen was invoked for this candidate. All values
above are expected static oracles pending qualified pure-Simple execution.
