# `right: auto` is not honoured on an absolutely positioned box (2026-09-14)

Found while landing round 22's shrink-to-fit fix for `width: auto` absolute
boxes (`absolute_auto_width_shrink_to_fit_spec.spl`). It is a **separate**
defect from that one and was deliberately filed rather than folded into that
change.

## Shape

A `position: absolute` box whose class sets `right: 10px` and whose inline style
overrides it with `right: auto; left: 10px`:

```html
<div class="positioned">Relative container
  <span class="badge" style="right:auto;left:10px">absolute</span></div>
```

| | width |
|---|---|
| Chrome 152 (`--headless=new --window-size=900,20000`) | **77** |
| Simple, after the round-22 shrink-to-fit fix | **890** |

Chrome's computed style on that element reads `left: 10px` and a *used*
`right: 813.5px` — the resolved value, not a specified one.

890 is exactly the `available` clamp computed by the new shrink-to-fit arm
(`padding_box_w - left_px` = 900 − 10). So the arm is running; what is wrong is
that `right: auto` did not clear the `right: 10px` inherited from the class.
Whether `right_px` keeps the class's 10, or `auto` parses to a value that is
neither "specified" nor the unspecified sentinel, is not yet determined — the
symptom is consistent with the max-content measurement being skipped entirely
for this box, since a correct shrink-to-fit would give 76 (see below) regardless
of the clamp.

The same box written WITHOUT any `right` declaration lays out correctly:

```html
<span style="position:absolute;left:10px;top:10px;padding:4px 8px">absolute</span>
```

gives 76 against Chrome's 77 — the ordinary 1 px text-advance residue — which is
what `AC-2` in the spec asserts. That contrast is the evidence that the width
arm is sound and the `auto` keyword handling is not.

## Why it was not fixed in round 22

The round's change is confined to `absolute_outer_width`'s missing
shrink-to-fit arm. Clearing `right_px` on `auto` is a change to offset parsing
in the declaration-apply layer, with its own blast radius over `left`, `top`,
`bottom` and the both-offsets-given stretch arm (which keys on
`st.left_px > 0 and st.right_px >= 0` and would start behaving differently for
any box that writes `auto` on one side). That deserves its own measurement,
fixture and controls.

No catalog page exercises it: the catalog's single absolutely positioned element
does not write `auto` on an offset, so this is invisible to the 8-page geometry
differ and costs 0 Σ today.

## Repro

`/private/tmp/.../r22/probe3.html` in the round-22 scratchpad, or directly:
the fixture in the spec's AC-2 comment. Harvest with
`scripts/check/check-chrome-layout-geometry-diff.shs`'s Chrome invocation.

## Related

* `doc/10_metrics/ui/web_chrome_parity_round22_2026-09-14.md` — the round that
  found it.
* `test/01_unit/browser_engine/absolute_auto_width_shrink_to_fit_spec.spl` —
  header records it as residue 2; AC-2 routes around it deliberately.
