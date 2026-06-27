# HTML/CSS Full Rendering Goal Status - Aspect Ratio Refresh

Date: 2026-06-27

## Scope

This report records the bounded Linux evidence for moving `aspect-ratio` from
unsupported CSS inventory into the implemented Simple Web CSS subset.

## Evidence

Command:

```sh
BUILD_DIR=build/html-css-full-rendering-aspect-ratio \
REPORT_PATH=build/html-css-full-rendering-aspect-ratio/report.md \
HTML_CSS_RENDERING_MANIFEST_FETCH=0 \
sh scripts/check/check-html-css-full-rendering-goal-status.shs
```

Result: exit code `0`.

Key rows:

- `html_css_full_rendering_goal_status=incomplete`
- `html_css_full_rendering_goal_html_tag_rendered_count=105`
- `html_css_full_rendering_goal_implemented_css_total_count=132`
- `html_css_full_rendering_goal_implemented_css_rendered_count=132`
- `html_css_full_rendering_goal_full_css_total_count=394`
- `html_css_full_rendering_goal_full_css_rendered_count=132`
- `html_css_full_rendering_goal_full_css_unrendered_count=262`
- `html_css_full_rendering_goal_unsupported_css_inventory_count=269`
- `html_css_full_rendering_goal_animation_css_status=pass`

## Interpretation

`aspect-ratio` is now part of the implemented Simple Web CSS subset and is
covered by both a focused unit renderer scenario and the full rendering goal
status spec. The broad full-CSS objective remains incomplete: 262 W3C CSS
inventory properties still need rendered behavior and evidence.

This does not close platform GPU capture work. Linux Vulkan RenderDoc `.rdc`,
macOS Metal, Windows D3D12, and strict native render-log comparison remain
separate host-verification lanes.
