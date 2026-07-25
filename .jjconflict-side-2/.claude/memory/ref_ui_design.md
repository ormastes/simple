---
name: UI Design System Reference
description: iOS-inspired design tokens, semantic colors, typography, spacing, components, TUI degradation
type: reference
---

## Semantic Colors
- `system_blue` (#007AFF) — primary actions, links
- `system_green` (#34C759) — success, toggle on
- `system_red` (#FF3B30) — destructive, errors
- `system_orange` (#FF9500) — warnings
- Labels: `label_primary` (100%), `label_secondary` (60%), `label_tertiary` (30%), `label_quaternary` (18%)
- Backgrounds: `bg_primary`, `bg_secondary` (grouped), `bg_tertiary` (cards)

## Typography (SF Pro)
| Style | Size | Weight | Use |
|-------|------|--------|-----|
| largeTitle | 34px | Bold | Screen titles |
| title1/2/3 | 28/22/20px | Bold/Semibold | Headers |
| body | 17px | Regular | Default content |
| footnote | 13px | Regular | Secondary |
| caption1/2 | 12/11px | Regular | Smallest |

## Spacing (4pt grid)
s1=4, s2=8, s3=12, s4=16, s5=20, s6=24, s8=32, s10=40, s12=48

## Corner Radius
sm=8, md=12, lg=16, xl=20, full=9999 (circular)

## Components
- `navigation_bar(id, title, left, right)` — top bar
- `tab_bar(id, items)` — bottom nav (2-5 items)
- `card(id, title, children)` — rounded container
- `switch_toggle(id, label, on)` — iOS toggle
- `segmented_control(id, items, selected)` — pill selector
- `search_bar(id, placeholder, value)` — search input

## TUI Degradation
Rounded corners → square, shadows → ignored, blur → ignored, animations → instant

## Theme
```simple
use common.ui.ios_theme.{ios_light, ios_dark}
```

## Files
`src/lib/common/ui/` — design_tokens.spl, ios_theme.spl, ios_css.spl, ios_icons.spl, ios_builder.spl
