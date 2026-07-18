# HTML/CSS Full Rendering Goal Status - Object Position Slice - 2026-06-27

## Scope

This report records the narrow Simple Web CSS `object-position` implementation
slice. It does not claim full CSS completion or native platform capture
completion.

## Command

```sh
BUILD_DIR=build/html-css-full-rendering-object-position \
REPORT_PATH=build/html-css-full-rendering-object-position/report.md \
HTML_CSS_RENDERING_MANIFEST_FETCH=0 \
sh scripts/check/check-html-css-full-rendering-goal-status.shs
```

## Result

- Exit code: 0
- `html_css_full_rendering_goal_status=incomplete`
- `html_css_full_rendering_goal_implemented_css_status=pass`
- `html_css_full_rendering_goal_all_implemented_css_ready_status=pass`
- `html_css_full_rendering_goal_implemented_css_total_count=134`
- `html_css_full_rendering_goal_implemented_css_rendered_count=134`
- `html_css_full_rendering_goal_full_css_total_count=394`
- `html_css_full_rendering_goal_full_css_rendered_count=134`
- `html_css_full_rendering_goal_full_css_unrendered_count=260`
- `html_css_full_rendering_goal_unsupported_css_inventory_count=267`

## Remaining Blockers

Full CSS remains incomplete. Native RenderDoc `.rdc`, Linux/macOS/Windows
render-log comparison, and platform capture lanes remain separate blockers.
