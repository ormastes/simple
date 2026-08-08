# CSS Grid auto-size item stretch

> Static candidate manual — runtime unclaimed. This document is hand-reviewed
> against the executable SSpec; it is not current docgen or runtime PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Fixture

```html
<style>
html,body{margin:0;width:8px;height:4px;background:#fff}
#grid{display:grid;width:8px;grid-template-columns:4px 4px;
  grid-template-rows:4px;gap:0;align-items:stretch}
#red{background:#dc2626}
#blue{background:#2563eb}
</style>
<main id="grid"><div id="red"></div><div id="blue"></div></main>
```

## Parse the styled HTML fixture

Expected semantic nodes are `main#grid`, `div#red`, and `div#blue`. The
composition source kind is expected to be `html_ast`.

## Resolve semantic layout and computed style

Expected primary computed values:

| Node | display | height auto | alignment | box `[x,y,w,h]` |
|---|---|---:|---|---|
| `grid` | `grid` | — | `align-items:stretch` | `[0,0,8,4]` |
| `red` | block | true | `align-self:auto` | `[0,0,4,4]` |
| `blue` | block | true | `align-self:auto` | `[4,0,4,4]` |

Expected controls:

| Control | Expected box | Contract |
|---|---|---|
| `align-self:start` | `[0,0,4,1]` | non-stretch alignment |
| `margin-top:auto` | `[4,0,4,1]` | auto margin owns free space |
| `height:2px` | `[8,0,4,2]` | authored height wins |
| content box + edges | `[12,1,4,6]` | edges deducted correctly |
| `height:0px` | `[16,0,4,1]` | numeric zero is not `auto` |
| two-column span | `[0,8,8,1]` | single-track stretch only |
| explicit-stretch `video` | `[8,8,4,1]` | replaced element excluded |
| stylesheet `height:0px` + inline `visibility` | `[12,8,4,1]` | size/alignment metadata survives full reconstruction |
| two-row span | `[16,8,4,1]` | single-track stretch only |
| vertical `inline-size:0px` | `[0,16,4,1]` | final writing mode maps physical height, non-auto |
| horizontal `block-size:0px` | `[4,16,4,1]` | final writing mode maps physical height, non-auto |

The nested automatic-height Grid is expected at `[0,0,4,4]`, retaining
`grid-template-columns:2px 2px` and `grid-template-rows:4px`; its children are
expected at `[0,0,2,4]` and `[2,0,2,4]`.

For non-replaced items with `width:2px;aspect-ratio:1/1`, `align-self:normal`
is expected to preserve the derived `[0,0,2,2]` box, while explicit
`align-self:stretch` is expected to produce `[4,0,2,4]` because the authored
height is still auto.

When the container omits `align-items`, its legacy stored value remains
`stretch` but `align_items_authored` is false. The aspect-ratio child therefore
follows Grid initial `normal` behavior and is expected at `[0,0,2,2]` rather
than stretching.

## Emit canonical Draw IR

Expected commands are ordinary canonical `rect` commands:

| Component | Geometry `[x,y,w,h]` | Color | Parent |
|---|---|---|---|
| `grid` | `[0,0,8,4]` | background-defined | document owner |
| `red` | `[0,0,4,4]` | `0xFFDC2626` | `grid` |
| `blue` | `[4,0,4,4]` | `0xFF2563EB` | `grid` |

The expected clip is `[0,0,8,4]`. The `grid` command carries computed
`display:grid`, `grid-template-rows:4px`, and `align-items:stretch`. No
Grid-specific Draw IR command or private painter is introduced.

## Render exact Engine2D pixels

Expected skipped-command count: `0`.

Expected full 8-by-4 framebuffer (all 32 pixels):

```text
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB
0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFFDC2626 0xFF2563EB 0xFF2563EB 0xFF2563EB 0xFF2563EB
```

## Claim boundary

This slice claims single-row, single-column non-replaced stretch using explicit
pixel tracks. Stretching spans, implicit rows, intrinsic/flexible tracks,
replaced-element stretch, auto-margin distribution, center/end positioning,
and full CSS Grid/WPT parity remain excluded.

The fail-closed replaced classification includes `audio`, `button`, `canvas`,
`embed`, `iframe`, `img`, `input`, `meter`, `object`, `progress`, `select`,
`textarea`, and `video`. The executable boundary control uses `video`.

## Evidence provenance

No qualified pure-Simple execution is retained for this correction cycle. An
earlier invocation used
`bin/release/x86_64-unknown-linux-gnu/simple`, SHA-256
`ea4af9a4498297e3c4f31ca74082c20ebb10d7d2cc65218cea022960e15e597d`, and
emitted a bootstrap-seed warning. Its exact version and durable log were not
recorded, so both that run and its docgen output are diagnostic only. Every
value above is an expected static oracle, not an observed PASS.
