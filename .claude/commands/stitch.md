# Stitch Skill -- Glassmorphism UI Screen Generation

Generate desktop OS UI screens via Google Stitch MCP with a macOS-inspired glassmorphism design system. All CSS patterns are license-free (standard glassmorphism, no proprietary assets).

## Prerequisites

| Artifact | Check | If Missing |
|----------|-------|------------|
| Stitch MCP | `.mcp.json` has `stitch` entry | Configure streamable-http transport |
| Stitch API key | `STITCH_API_KEY` env var | Get from stitch.withgoogle.com Settings |
| Glass tokens | `src/lib/common/ui/glass_tokens.spl` | Already exists |
| Glass numeric | `src/lib/common/ui/glass_numeric_tokens.spl` | Already exists |

## When to Use

- Generating UI mockups or visual prototypes for Simple OS
- Creating reference screens for new WM features
- Exploring design variants (layout, color, light/dark)
- Producing desktop-quality glassmorphism screenshots

## Design System Configuration

Derived from `glass_numeric_tokens.spl` and `glass_tokens.spl`:

```
displayName: "SimpleOS Glass"
colorMode: DARK
headlineFont: MANROPE
bodyFont: INTER
labelFont: SPACE_GROTESK
roundness: ROUND_TWELVE
customColor: "#0A84FF"
colorVariant: TONAL_SPOT
overridePrimaryColor: "#0A84FF"
overrideSecondaryColor: "#BB86FC"
overrideTertiaryColor: "#30D158"
overrideNeutralColor: "#1E1E23"
```

### Typography Scale

```json
{
  "display-lg": { "fontFamily": "Manrope", "fontSize": "34px", "fontWeight": "700", "lineHeight": "1.2", "letterSpacing": "-0.01em" },
  "display-md": { "fontFamily": "Manrope", "fontSize": "28px", "fontWeight": "700", "lineHeight": "1.25", "letterSpacing": "-0.01em" },
  "title-lg": { "fontFamily": "Manrope", "fontSize": "22px", "fontWeight": "600", "lineHeight": "1.3" },
  "title-md": { "fontFamily": "Manrope", "fontSize": "17px", "fontWeight": "600", "lineHeight": "1.35" },
  "body-lg": { "fontFamily": "Inter", "fontSize": "17px", "fontWeight": "400", "lineHeight": "1.5" },
  "body-md": { "fontFamily": "Inter", "fontSize": "15px", "fontWeight": "400", "lineHeight": "1.5" },
  "body-sm": { "fontFamily": "Inter", "fontSize": "13px", "fontWeight": "400", "lineHeight": "1.4" },
  "label-lg": { "fontFamily": "Space Grotesk", "fontSize": "13px", "fontWeight": "500", "lineHeight": "1.4" },
  "label-sm": { "fontFamily": "Space Grotesk", "fontSize": "11px", "fontWeight": "500", "lineHeight": "1.3", "letterSpacing": "0.02em" }
}
```

### Spacing Scale

```json
{ "xs": "4px", "sm": "8px", "md": "12px", "lg": "20px", "xl": "32px" }
```

## designMd (Glassmorphism CSS Rules)

This markdown is passed as the `designMd` field in `create_design_system`. It teaches the model the full glassmorphism design language:

```markdown
# SimpleOS Glassmorphism Design Language

## Core Principle
Every surface is a frosted glass pane floating over a deep-space gradient background.
No flat solid backgrounds. All surfaces use semi-transparent backgrounds with backdrop-filter blur.

## Background
- Dark gradient from #060612 (top) to #1A0830 (bottom) -- deep space feel
- Light gradient from #C8B8E8 (top lavender) to #F0ECF5 (bottom soft white)

## Glass Surfaces (Dark Mode)
- Primary: rgba(30,30,35,0.72) with backdrop-filter: blur(20px)
- Secondary: rgba(40,40,48,0.52) with backdrop-filter: blur(20px)
- Tertiary: rgba(50,50,58,0.36) with backdrop-filter: blur(8px)
- Elevated (modals, popovers): rgba(44,44,50,0.88) with backdrop-filter: blur(40px)

## Glass Surfaces (Light Mode)
- Primary: rgba(255,255,255,0.72) with backdrop-filter: blur(20px)
- Secondary: rgba(255,255,255,0.52) with backdrop-filter: blur(20px)
- Tertiary: rgba(255,255,255,0.36) with backdrop-filter: blur(8px)
- Elevated: rgba(255,255,255,0.85) with backdrop-filter: blur(40px)

## Borders
- Subtle: 1px solid rgba(255,255,255,0.08) -- barely visible glass edge
- Prominent: 1px solid rgba(255,255,255,0.18) -- active/focused elements
- Top edge highlight: 1px rgba(255,255,255,0.30) on top border for light-catch effect

## Shadows (multi-layer depth)
- Active windows: 9+ shadow layers creating realistic depth
- Layer pattern: wide soft (20px blur, low alpha) + blue tint + tight contact + bottom accent + ambient halo
- Inactive windows: 3 layers, reduced alpha

## Window Chrome
- Title bar: 24px, glass surface with blur, traffic light buttons (close #FF5F57, minimize #FFBD2E, maximize #28CA41) on left
- Title text centered, 13px, secondary text color
- 12px corner radius on window frame

## System Bar (top, 28px)
- Full-width glass surface, blur(24px), nav-grade
- Left: Logo + active app name + menu items (File, Edit, View, Go, Window)
- Right: Search icon, Control Center, Wi-Fi, battery %, volume, clock
- Bottom separator: 1px border with accent color undertone

## Dock (bottom)
- Pill-shaped glass container, 58px tall, 26px corner radius
- Icons: 40px with 48px pill background, 16px gap
- Magnification on hover (scale 1.0 to 1.5)
- Bounce animation for launching apps
- Active indicator: 4px dot below icon
- Apps: Terminal, Files, Calculator, Clock, Settings, Browser, Editor

## Typography
- System font stack, 15px base body size
- Headline weight: 600-700, body weight: 400, label weight: 500
- Text primary: #F5F5F7 (dark) / #1D1D1F (light)
- Text secondary: rgba(235,235,245,0.6) (dark) / rgba(60,60,67,0.6) (light)

## Colors
- Accent: #0A84FF (iOS blue)
- Secondary accent: #BB86FC (purple)
- Semantic: error #FF453A, warning #FF9F0A, success #30D158, info #64D2FF

## Interactions
- Hover: border transitions to prominent, shadow upgrades by one tier
- Active: scale(0.98) press effect
- Focus: 3px accent-color ring with 0.2 alpha
- Transitions: 150ms fast, 300ms normal, cubic-bezier(0.4, 0.0, 0.2, 1.0)

## Layout Patterns
- Flex layout with spacers
- Cards with glass surface + subtle border + small shadow
- Lists with hover-highlight rows
- Sidebars: secondary glass surface, 200-240px wide
- Toolbars: primary glass surface with nav blur

## DO NOT
- Use flat solid colored backgrounds
- Use sharp corners (minimum 8px radius)
- Use heavy drop shadows without blur
- Use bright white or pure black surfaces
- Forget the gradient background behind all glass layers
```

## Workflow

### Phase 1: Create Project
```
mcp__stitch__create_project(title: "SimpleOS Glass UI")
```

### Phase 2: Create Design System
```
mcp__stitch__create_design_system(
  projectId: "<id>",
  designSystem: {
    displayName: "SimpleOS Glass",
    theme: { <all config above + designMd + typography + spacing> }
  }
)
```
Then `update_design_system` to activate.

### Phase 3: Generate Screens
Use `generate_screen_from_text` with curated prompts below. Always:
- `deviceType: "DESKTOP"`
- `modelId: "GEMINI_3_1_PRO"`
- One screen at a time (each takes 1-3 min, do NOT retry)

### Phase 4: Apply Design System
```
mcp__stitch__apply_design_system(projectId, assetId, selectedScreenInstances)
```
Get instance IDs from `get_project` first.

### Phase 5: Variants
```
mcp__stitch__generate_variants(
  creativeRange: "REFINE",
  aspects: ["COLOR_SCHEME"],
  variantCount: 2
)
```

## Screen Prompt Templates

### Desktop / Launcher
```
Design a macOS-inspired desktop OS home screen with glassmorphism effects.

Background: Deep space gradient from dark navy-purple (#060612) at top to deep violet (#1A0830) at bottom.

Top system bar (28px tall): Frosted glass surface with blur, showing a small logo left, app name "Finder", menu items (File, Edit, View, Go, Window, Help) in 13px text. Right side: search icon, control center grid icon, Wi-Fi icon, battery percentage "97%", volume icon, and clock "9:41 AM". Subtle bottom border separator.

Main desktop area: Empty with just the gradient background showing through. Optional: 2-3 desktop file/folder icons in a grid aligned to top-right.

Bottom dock: Pill-shaped frosted glass container centered at bottom with 6px margin. Contains 7 app icons as rounded squares (40px) with labels below: Terminal (blue), Files (green), Calculator (red), Clock (orange), Settings (purple), Browser (orange), Editor (teal). Active dot indicator below Terminal icon.

Style: All surfaces use semi-transparent backgrounds (rgba with 0.72 opacity) and backdrop-filter blur. Borders are 1px rgba(255,255,255,0.08). Corner radius 12px for windows, 26px for dock pill. Multi-layer drop shadows. Dark mode with #F5F5F7 text.
```

### Window Manager (3 Windows)
```
Design a desktop OS window manager showing 3 overlapping glassmorphism windows on a dark gradient background.

Background: Deep space gradient (#060612 to #1A0830).

System bar at top: Frosted glass, 28px, showing "Editor" app name, File/Edit/View menus, clock and status icons on right.

Window 1 (focused, front): "Editor" window, 500x350px, centered-right. Title bar with traffic light buttons (red #FF5F57, yellow #FFBD2E, green #28CA41) on left, "Editor" title centered. Window body shows a code editor with syntax-highlighted code (blue keywords, green strings, white identifiers) on a frosted glass surface. Multi-layer drop shadows (9 layers, soft blur).

Window 2 (behind, left): "Terminal" window, 450x300px, offset left. Frosted glass surface showing a terminal with green prompt "simpleos$", white command text, and command output. Dimmed slightly (inactive state). Reduced shadow layers.

Window 3 (behind, right): "File Manager" window, 400x280px, partially hidden. Shows a sidebar with folder list and main area with file icons in a grid. Inactive state.

Bottom dock: Glass pill with 7 app icons, Terminal and Editor showing active indicators (dots).

Style: Semi-transparent surfaces, backdrop-filter blur(20px), 12px corner radius on windows, subtle rgba(255,255,255,0.08) borders, text in #F5F5F7. Focused window has prominent borders and stronger shadows.
```

### Settings Panel
```
Design a macOS-style System Settings panel as a glassmorphism desktop window.

Background: Deep space gradient (#060612 to #1A0830).

System bar at top: Frosted glass showing "Settings" app name.

Settings window (600x450px, centered): Frosted glass surface with 12px corner radius, traffic light buttons, "Settings" title centered in title bar.

Left sidebar (200px wide): Secondary glass surface (rgba(40,40,48,0.52)). Navigation items as a vertical list: "General" (selected, highlighted with accent blue #0A84FF background), "Appearance", "Display", "Sound", "Network", "Bluetooth", "Keyboard", "Mouse", "Storage". Each item 36px tall with icon and label.

Right content area: Shows "General" settings panel with card-based layout:
- Card 1: "About This Computer" -- SimpleOS v1.0, processor info, memory
- Card 2: "Appearance" toggle -- Dark/Light mode switch with preview circles
- Card 3: "Desktop & Dock" -- Dock size slider, magnification toggle
Each card is a tertiary glass surface with subtle border, 12px radius, internal padding.

Bottom dock: Glass pill with active indicator on Settings icon.

Style: Nested glass layers -- window surface over sidebar surface over card surfaces. Each layer progressively more translucent. All corners rounded. Subtle borders.
```

### File Manager
```
Design a macOS Finder-style file manager as a glassmorphism desktop window.

Background: Deep space gradient (#060612 to #1A0830).

System bar at top: Frosted glass showing "Finder" app name with File/Edit/View/Go menus.

File Manager window (550x400px, centered): Frosted glass surface, traffic light buttons, title "Documents".

Toolbar (40px): Glass surface below title bar with navigation buttons (back, forward arrows), view mode toggles (icon/list/column icons), search field (glass input with magnifying glass icon, placeholder "Search", 8px radius).

Left sidebar (180px): Secondary glass surface. Sections with headers:
- "Favorites": Desktop, Documents, Downloads, Applications (folder icons, blue accent on selected "Documents")
- "Locations": SimpleOS HD, Network (disk/network icons)
- "Tags": Red, Blue, Green, Orange (colored circles)

Main content area: Grid view showing 12 file/folder items in a 4x3 grid:
- Folders: Projects (blue), Photos (green), Music (orange), Code (teal)
- Files: readme.txt (document icon), image.png (image preview), notes.md, config.spl
Each item shows icon (48px) + name below + file size in tertiary text.

Status bar (24px bottom): Glass surface showing "8 items, 2.3 GB available".

Bottom dock with active Files indicator.

Style: Layered glass surfaces with increasing translucency. Sidebar items have hover state. Selected folder has accent blue highlight. Grid items have subtle hover card elevation.
```

## Critical Rules

1. Always use `GEMINI_3_1_PRO` -- highest quality output
2. Always `deviceType: "DESKTOP"` for all screens
3. Create design system BEFORE generating screens
4. After `create_design_system`, call `update_design_system` to activate
5. One screen at a time -- each takes 1-3 min, do NOT retry on timeout
6. Use `edit_screens` for small focused changes, never full rewrites
7. The `designMd` field is the most powerful quality lever
8. For light mode: use `generate_variants` with `aspects: ["COLOR_SCHEME"]`
9. All colors from `glass_tokens.spl` / `glass_numeric_tokens.spl`
10. No license issues -- all CSS glassmorphism is open standard

## Outputs

| Artifact | Location |
|----------|----------|
| Stitch project | Cloud (project ID in output) |
| Design system | Cloud (asset ID in output) |
| Screen designs | Stitch cloud (screen IDs in output) |
| Screen code | `mcp__stitch__get_screen` to retrieve |
