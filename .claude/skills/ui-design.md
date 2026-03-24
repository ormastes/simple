# UI Design Skill - iOS-Inspired Design System

## Design Principles

### Clarity
- Content is the focus; chrome recedes
- Use whitespace generously (4pt grid)
- Typography creates hierarchy, not decoration
- Every pixel serves a purpose

### Deference
- UI defers to content with translucent materials
- Subtle depth via shadows, not heavy borders
- Motion is purposeful, never gratuitous
- System colors adapt to context automatically

### Depth
- Layered surfaces create spatial relationships
- Blur effects show content beneath overlays
- Shadows indicate elevation consistently
- Z-index scale: base(0) < sticky(10) < nav(50) < overlay(100) < sheet(200) < modal(300) < alert(400)

## Color System

### Semantic Colors
Use semantic names, never raw hex values in app code:
- `system_blue` (#007AFF / #0A84FF) — Default tint, links, primary actions
- `system_green` (#34C759 / #30D158) — Success, positive, toggle on
- `system_red` (#FF3B30 / #FF453A) — Destructive, errors
- `system_orange` (#FF9500 / #FF9F0A) — Warnings, attention
- `system_yellow` (#FFCC00 / #FFD60A) — Highlights
- `system_purple` (#AF52DE / #BF5AF2) — Decorative accent
- `system_indigo` (#5856D6 / #5E5CE6) — Brand accent
- `system_teal` (#5AC8FA / #64D2FF) — Informational
- `system_pink` (#FF2D55 / #FF375F) — Secondary destructive

### Background Layers
- `bg_primary` — Main screen background
- `bg_secondary` — Grouped table background (Settings-style)
- `bg_tertiary` — Card/cell background within groups
- `bg_grouped` — Synonym for bg_secondary
- `bg_grouped_secondary` — Cells within grouped sections

### Label Colors (opacity-based hierarchy)
- `label_primary` — Primary text (full opacity)
- `label_secondary` — Secondary text (60% opacity)
- `label_tertiary` — Tertiary text (30% opacity)
- `label_quaternary` — Placeholder text (18% opacity)

### Fill Levels
- `fill_primary` through `fill_quaternary` — Progressively lighter fills for controls

### Theme Selection
```simple
use common.ui.ios_theme.{ios_light, ios_dark}
val theme = ios_dark()
val tree = build_tree_with_title(root, "My App", "ios_dark")
```

## Typography Scale

| Style | Size | Weight | Use |
|-------|------|--------|-----|
| largeTitle | 34px | Bold | Screen titles (navigation large title) |
| title1 | 28px | Bold | Section headers |
| title2 | 22px | Bold | Subsection headers |
| title3 | 20px | Semibold | Tertiary headers |
| headline | 17px | Semibold | Emphasized body text |
| body | 17px | Regular | Primary content (DEFAULT) |
| callout | 16px | Regular | Secondary content |
| subheadline | 15px | Regular | Labels, captions |
| footnote | 13px | Regular | Secondary info |
| caption1 | 12px | Regular | Tertiary labels |
| caption2 | 11px | Regular | Smallest text |

Font stack: `-apple-system, BlinkMacSystemFont, 'SF Pro Text', system-ui, sans-serif`

## Spacing (4pt Grid)

All spacing is a multiple of 4px:
- `s0`: 0px — No spacing
- `s1`: 4px — Tight (icon gaps)
- `s2`: 8px — Compact (list padding)
- `s3`: 12px — Default (cell padding)
- `s4`: 16px — Comfortable (section spacing)
- `s5`: 20px — Generous (card padding)
- `s6`: 24px — Screen margins
- `s8`: 32px — Section gaps
- `s10`: 40px — Large gaps
- `s12`: 48px — Extra-large

Rule: When in doubt, use multiples of 8px.

## Corner Radius

- `none` (0) — No rounding
- `sm` (8px) — Small controls, badges
- `md` (12px) — Buttons, inputs, cards
- `lg` (16px) — Large panels
- `xl` (20px) — Bottom sheets
- `full` (9999px) — Circular (avatars, pills)

## Shadows (Elevation)

- `none` — Flat content
- `sm` — Subtle lift (list items, cards at rest)
- `md` — Popovers, floating buttons
- `lg` — Bottom sheets, modals
- `xl` — Top-level overlays, alerts

## Component Catalog

### NavigationBar (`navigation_bar`)
Top bar with title, optional back button and action buttons.
```simple
navigation_bar("nav", "Settings", ["back"], ["done"])
```
- Large title collapses on scroll (web only)
- Translucent backdrop blur
- TUI: Bold centered title in single row

### Bottom TabBar (`tab_bar`)
Fixed bottom navigation with icon + label.
```simple
tab_bar("tabs", [tab_item("home", "house", "Home"), tab_item("search", "magnifyingglass", "Search")])
```
- 2-5 items, active item tinted with accent
- Badge support for notification counts
- TUI: Bottom row `[icon label | icon label]`

### Card (`card`)
Rounded container with shadow.
```simple
card("info_card", "Title", [text_widget("body", "Content here")])
```
- Rounded corners (md), shadow (sm)
- Optional title and subtitle
- TUI: Panel with border

### Switch/Toggle (`switch`)
iOS-style on/off toggle.
```simple
switch_toggle("notifications", "Enable Notifications", true)
```
- Green track when on, gray when off
- Animated thumb slide (web)
- TUI: `[ON ]` / `[ OFF]`

### SegmentedControl (`segmented_control`)
Horizontal pill-style mutually exclusive selection.
```simple
segmented_control("view", ["Board", "List", "Calendar"], 0)
```
- Rounded pill container
- Sliding selection indicator
- TUI: `[*Board* | List | Calendar]`

### SearchBar (`search_bar`)
Rounded input with magnifying glass icon.
```simple
search_bar("search", "Search...", "")
```
- Magnifying glass prefix icon
- Optional cancel button
- TUI: `[magnifier] Search...`

## Icon System

Use `ios_icon(name)` for Unicode icons:
```simple
use common.ui.ios_icons.{ios_icon}
val icon = ios_icon("checkmark")  # returns "✓"
```

Common icons: `house`, `gear`, `magnifyingglass`, `star`, `star.fill`, `heart`, `trash`, `pencil`, `folder`, `doc`, `envelope`, `calendar`, `clock`, `plus`, `minus`, `checkmark`, `xmark`, `chevron.right`, `chevron.left`, `bold`, `italic`, `underline`

## Layout Patterns

### Settings Page (Grouped List)
```simple
column("settings", [
    navigation_bar("nav", "Settings", [], []),
    scroll("content", 30, [
        panel("group1", "General", [
            # list items with disclosure chevrons
        ]),
        panel("group2", "Notifications", [
            # switch toggles
        ])
    ])
])
```

### Master-Detail (3-Column)
```simple
row("main", [
    with_flex(panel("sidebar", "Folders", [...]), 1),
    with_flex(panel("list", "", [...]), 2),
    with_flex(panel("detail", "", [...]), 3)
])
```

### Tab-Based Navigation
```simple
column("app", [
    # Content area changes based on active tab
    panel("content", "", [current_view_widgets]),
    tab_bar("tabs", [
        tab_item("home", "house", "Home"),
        tab_item("search", "magnifyingglass", "Search"),
        tab_item("profile", "person", "Profile")
    ])
])
```

## TUI Degradation Rules

| iOS Widget | TUI Rendering |
|-----------|---------------|
| NavigationBar | Bold centered title, `<` back arrow |
| TabBar | Bottom row: `icon label \| icon label` |
| Card | Panel with single-line border |
| Switch | `[ON ]` green / `[ OFF]` dim |
| SegmentedControl | `[*Active* \| Item2 \| Item3]` bold active |
| SearchBar | `[magnifier] placeholder` underlined |
| Rounded corners | Ignored (square borders) |
| Shadows | Ignored |
| Blur/translucency | Ignored |
| Animations | Instant transitions |

## Accessibility Checklist

- Minimum touch target: 44x44pt (web CSS `min-height: 44px`)
- Color contrast: 4.5:1 for body text, 3:1 for large text
- All interactive elements focusable via keyboard (Tab/Shift+Tab)
- Focus indicators visible (3px accent ring)
- aria-label on icon-only buttons
- aria-role on custom controls (switch -> role="switch")
- Reduced motion: respect `prefers-reduced-motion` media query
- High contrast mode: use opaque colors, thicker borders

## File Structure

```
src/lib/common/ui/
  design_tokens.spl    # IOSDesignTokens, color/typography/spacing/radius/shadow classes
  ios_theme.spl        # ios_light(), ios_dark() UITheme factories
  ios_css.spl          # generate_ios_css() CSS generation
  ios_icons.spl        # ios_icon() Unicode lookup
  ios_builder.spl      # Builders for iOS-specific widgets (Phase 1)
```

## See Also
- `/design` — Type system, module design, patterns
- `/coding` — Language rules, variable conventions
- `doc/guide/library/ui.md` — Full UI framework guide
