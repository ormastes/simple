# CSS flex gap zero cascade

> This scenario proves both that a later valid `gap:0` declaration resets an earlier positive Flex gap and that a later malformed declaration does not erase an earlier valid `gap:4px`. Both cases cross the dispatch and full Style reconstruction paths; an invalid-only row remains the zero-gap control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

```html
<style>
html,body{margin:0;width:12px;height:22px;background:#fff}
.row{display:flex;width:12px;height:2px}
.positive{gap:4px}
.red{width:4px;height:2px;background:#dc2626}
.blue{width:4px;height:2px;background:#2563eb}
</style>
<div id="dispatch-row" class="row positive" style="gap:0">
  <div id="dispatch-red" class="red"></div>
  <div id="dispatch-blue" class="blue"></div>
</div>
<div id="full-row" class="row positive" style="gap:0;visibility:visible">
  <div id="full-red" class="red"></div>
  <div id="full-blue" class="blue"></div>
</div>
<div id="duplicate-dispatch-row" class="row" style="gap:4px;gap:bogus">
  <div id="duplicate-dispatch-red" class="red"></div>
  <div id="duplicate-dispatch-blue" class="blue"></div>
</div>
<div id="duplicate-full-row" class="row" style="gap:4px;gap:bogus;visibility:visible">
  <div id="duplicate-full-red" class="red"></div>
  <div id="duplicate-full-blue" class="blue"></div>
</div>
<div id="invalid-only-row" class="row" style="gap:bogus">
  <div id="invalid-only-red" class="red"></div>
  <div id="invalid-only-blue" class="blue"></div>
</div>
<div id="syntax-dispatch-row" class="row"
     style="gap:4px;gap:-9px;gap:7.5px;gap:8em;gap:10pxjunk">
  <div id="syntax-dispatch-red" class="red"></div>
  <div id="syntax-dispatch-blue" class="blue"></div>
</div>
<div id="syntax-full-row" class="row"
     style="gap:4px;gap:-9px;gap:7.5px;gap:8em;gap:10pxjunk;visibility:visible">
  <div id="syntax-full-red" class="red"></div>
  <div id="syntax-full-blue" class="blue"></div>
</div>
<div id="initial-row" class="row positive" style="gap:initial">
  <div id="initial-red" class="red"></div>
  <div id="initial-blue" class="blue"></div>
</div>
<div id="unset-row" class="row positive" style="gap:unset">
  <div id="unset-red" class="red"></div>
  <div id="unset-blue" class="blue"></div>
</div>
<div id="inherit-row" class="row positive" style="gap:inherit">
  <div id="inherit-red" class="red"></div>
  <div id="inherit-blue" class="blue"></div>
</div>
<div id="inherit-full-row" class="row positive"
     style="gap:inherit;visibility:visible">
  <div id="inherit-full-red" class="red"></div>
  <div id="inherit-full-blue" class="blue"></div>
</div>
```

</details>

Expected semantic row nodes are `div#dispatch-row`, `div#full-row`,
`div#duplicate-dispatch-row`, `div#duplicate-full-row`, and
`div#invalid-only-row`, both `syntax-*` rows, and the `initial`, `unset`, and
both `inherit` controls. The composition source kind is expected to be
`html_ast`.

## Related Documentation

The zero-reset rows expose `[gap_px,row_gap_px,column_gap_px]` as `[0,0,0]`.
Both duplicate-declaration rows expose `[4,4,4]`; the invalid-only negative
control exposes `[0,0,0]`. Both syntax rows retain `[4,4,4]` after rejecting
signed, decimal, foreign-unit, and trailing-junk duplicates. `initial` and
`unset` reset to `[0,0,0]`. Both terminal parent-default `inherit` controls
reset the positive class gap to zero through the dispatch and full
reconstruction paths; nonzero parent inheritance is not claimed because the
current Style input has no parent computed-gap channel.

| Component | Expected box `[x,y,w,h]` |
|---|---|
| `dispatch-row` | `[0,0,12,2]` |
| `dispatch-red` | `[0,0,4,2]` |
| `dispatch-blue` | `[4,0,4,2]` |
| `full-row` | `[0,2,12,2]` |
| `full-red` | `[0,2,4,2]` |
| `full-blue` | `[4,2,4,2]` |
| `duplicate-dispatch-row` | `[0,4,12,2]` |
| `duplicate-dispatch-red` | `[0,4,4,2]` |
| `duplicate-dispatch-blue` | `[8,4,4,2]` |
| `duplicate-full-row` | `[0,6,12,2]` |
| `duplicate-full-red` | `[0,6,4,2]` |
| `duplicate-full-blue` | `[8,6,4,2]` |
| `invalid-only-row` | `[0,8,12,2]` |
| `invalid-only-red` | `[0,8,4,2]` |
| `invalid-only-blue` | `[4,8,4,2]` |
| `syntax-dispatch-row` | `[0,10,12,2]` |
| `syntax-dispatch-red` | `[0,10,4,2]` |
| `syntax-dispatch-blue` | `[8,10,4,2]` |
| `syntax-full-row` | `[0,12,12,2]` |
| `syntax-full-red` | `[0,12,4,2]` |
| `syntax-full-blue` | `[8,12,4,2]` |
| `initial-row` | `[0,14,12,2]` |
| `initial-red` | `[0,14,4,2]` |
| `initial-blue` | `[4,14,4,2]` |
| `unset-row` | `[0,16,12,2]` |
| `unset-red` | `[0,16,4,2]` |
| `unset-blue` | `[4,16,4,2]` |
| `inherit-row` | `[0,18,12,2]` |
| `inherit-red` | `[0,18,4,2]` |
| `inherit-blue` | `[4,18,4,2]` |
| `inherit-full-row` | `[0,20,12,2]` |
| `inherit-full-red` | `[0,20,4,2]` |
| `inherit-full-blue` | `[4,20,4,2]` |

Requirements covered by the scenarios in this manual:

All twenty-two colored items are expected to remain ordinary canonical `rect`
commands. Red commands use `0xFFDC2626`; blue commands use `0xFF2563EB`.
Their command geometry exactly matches the child boxes above, proving that no
private painter or backend-specific gap correction is involved.

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6776f4067e9b779412f184cc5800e3e774745db0fcdbf235d456e7c493aba95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Expected full framebuffer length: `264`. Every pixel is checked. Each listed
pattern occupies both scanlines of its row, with `R=0xFFDC2626`,
`B=0xFF2563EB`, and `W=0xFFFFFFFF`.

| Row y | Exact 12-pixel pattern |
|---:|---|
| 0 | `RRRRBBBBWWWW` |
| 2 | `RRRRBBBBWWWW` |
| 4 | `RRRRWWWWBBBB` |
| 6 | `RRRRWWWWBBBB` |
| 8 | `RRRRBBBBWWWW` |
| 10 | `RRRRWWWWBBBB` |
| 12 | `RRRRWWWWBBBB` |
| 14 | `RRRRBBBBWWWW` |
| 16 | `RRRRBBBBWWWW` |
| 18 | `RRRRBBBBWWWW` |
| 20 | `RRRRBBBBWWWW` |

## Claim boundary

This scenario claims strict nonnegative integer/`px` parsing, last-valid
duplicate recovery, `initial`/`unset` reset, and terminal parent-default
`inherit` behavior for Flex `gap` through both declaration paths. General
nonzero `inherit`, `revert`, and `revert-layer` remain RED until parent
computed-gap and origin/layer provenance reach this owner. Percentage gaps,
multi-column `normal`, and complete CSS Box Alignment parity remain outside
this slice.

## Evidence provenance

No runtime, bootstrap, or docgen was invoked for this candidate. All values
above are expected static oracles pending qualified pure-Simple execution.
