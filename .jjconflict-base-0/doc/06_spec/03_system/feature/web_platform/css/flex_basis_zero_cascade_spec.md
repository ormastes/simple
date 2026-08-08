# CSS flex-basis zero cascade

> Static candidate manual — runtime unclaimed. This hand-reviewed mirror
> records expected oracles from the executable SSpec; it is not generated PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Fixture

```html
<style>
html,body{margin:0;width:10px;height:4px;background:#fff}
.row{display:flex;width:10px;height:2px}
.reset{width:2px;height:2px;flex-basis:6px;background:#dc2626}
.control{width:2px;height:2px;background:#2563eb}
</style>
<div id="dispatch-row" class="row">
  <div id="dispatch-reset" class="reset" style="flex-basis:0"></div>
  <div id="dispatch-control" class="control"></div>
</div>
<div id="full-row" class="row">
  <div id="full-reset" class="reset"
    style="flex-basis:0;visibility:visible"></div>
  <div id="full-control" class="control"></div>
</div>
```

## Parse the split-cascade flex-basis-zero fixture

Expected reset nodes are `div#dispatch-reset` and `div#full-reset`. The
composition source kind is `html_ast`.

## Resolve zero flex basis Web layout geometry

Both reset styles expose `flex_basis_px == 0`.

| Component | Expected box `[x,y,w,h]` |
|---|---|
| `dispatch-row` | `[0,0,10,2]` |
| `dispatch-reset` | `[0,0,2,2]` |
| `dispatch-control` | `[2,0,2,2]` |
| `full-row` | `[0,2,10,2]` |
| `full-reset` | `[0,2,2,2]` |
| `full-control` | `[2,2,2,2]` |

## Emit canonical Draw IR rectangles from WebIR

The four colored items remain canonical `rect` commands with the boxes above.
Reset items are `0xFFDC2626`; controls are `0xFF2563EB`. No private painter,
parallel IR, or backend command is introduced.

## Render exact flex-basis-zero Engine2D pixels

Expected skipped-command count: `0`.

Expected full 10-by-4 framebuffer (all 40 pixels):

```text
0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
```

The red items remaining two pixels wide proves the earlier six-pixel basis no
longer survives the cascade.

## Claim boundary and provenance

This bounded slice covers supported nonnegative integer/px basis reset through
both declaration paths. Complete Flex basis grammar is outside scope. No
runtime, bootstrap, or docgen was invoked; values are static expected oracles.
