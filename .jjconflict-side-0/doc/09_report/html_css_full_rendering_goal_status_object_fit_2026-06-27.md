# HTML/CSS Full Rendering Goal Status - Object Fit Refresh

Date: 2026-06-27

## Scope

This report records the bounded Linux evidence for moving `object-fit` from
unsupported CSS inventory into the implemented Simple Web CSS subset.

## Evidence

Command:

```sh
BUILD_DIR=build/html-css-full-rendering-object-fit \
REPORT_PATH=build/html-css-full-rendering-object-fit/report.md \
HTML_CSS_RENDERING_MANIFEST_FETCH=0 \
sh scripts/check/check-html-css-full-rendering-goal-status.shs
```

Result: exit code `0`.

Key rows:

- `html_css_full_rendering_goal_status=incomplete`
- `html_css_full_rendering_goal_html_tag_rendered_count=105`
- `html_css_full_rendering_goal_implemented_css_total_count=133`
- `html_css_full_rendering_goal_implemented_css_rendered_count=133`
- `html_css_full_rendering_goal_full_css_total_count=394`
- `html_css_full_rendering_goal_full_css_rendered_count=133`
- `html_css_full_rendering_goal_full_css_unrendered_count=261`
- `html_css_full_rendering_goal_unsupported_css_inventory_count=268`
- `html_css_full_rendering_goal_animation_css_status=pass`

## Interpretation

`object-fit` is now parsed into the Simple Web computed style and affects
rendered pixels for image placeholders. The focused renderer spec covers
`object-fit: contain` letterboxing, and the full rendering goal status gate
shows all implemented Simple Web CSS properties rendered in manifest fixtures.

The broad full-CSS objective remains incomplete: 261 W3C CSS inventory
properties still need rendered behavior and evidence. This report does not
close RenderDoc `.rdc`, Metal, D3D12, or strict native render-log comparison
lanes.
