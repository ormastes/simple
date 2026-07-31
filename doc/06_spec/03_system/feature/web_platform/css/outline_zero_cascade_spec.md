# CSS outline zero cascade

> Static candidate manual — runtime unclaimed. This hand-reviewed mirror
> records expected oracles from the executable SSpec; it is not generated PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Fixture

```html
<style>
html,body{margin:0;width:10px;height:6px;background:#fff}
.target{position:absolute;width:2px;height:2px;
  background:#2563eb;outline:1px solid #dc2626}
#dispatch{left:2px;top:2px}
#full{left:6px;top:2px}
</style>
<div id="dispatch" class="target" style="outline:0"></div>
<div id="full" class="target"
  style="outline:0;visibility:visible"></div>
```

## Parse the split-cascade outline-zero fixture

Expected semantic nodes are `div#dispatch` and `div#full`. The composition
source kind is expected to be `html_ast`.

## Resolve zero-width outline Web style and geometry

Both computed styles are expected to expose `outline_w == 0`.

| Component | Expected box `[x,y,w,h]` |
|---|---|
| `dispatch` | `[2,2,2,2]` |
| `full` | `[6,2,2,2]` |

The boxes stay unchanged because CSS outlines do not participate in layout.

## Emit canonical Draw IR without outline expansion

Both targets are expected to remain ordinary canonical `rect` commands with
color `0xFF2563EB`, geometry matching the table, and computed
`outline-width:0`. No special outline command or private painter is added.

## Render exact outline-zero Engine2D pixels

Expected skipped-command count: `0`.

Expected full 10-by-6 framebuffer (all 60 pixels):

```text
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF 0xFF2563EB 0xFF2563EB 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
```

The absence of `0xFFDC2626` proves the earlier red outline no longer paints.

## Claim boundary

This bounded slice claims supported integer/px zero shorthand reset behavior
through the two declaration paths. Complete outline shorthand grammar,
focus-ring policy, CSS-wide keyword semantics, and non-pixel lengths remain
outside scope.

## Evidence provenance

No runtime, bootstrap, or docgen was invoked. Every value above is an expected
static oracle pending qualified pure-Simple execution.
