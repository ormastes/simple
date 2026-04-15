# SimpleOS Stitch Design System Reference

> Extracted from Stitch MCP projects (2026-04-09).
> Source of truth for consistent theme/UI creation across GUI lib and window manager.

---

## 1. Stitch Projects & Design Systems

### Project A: "Simple OS UI" (Evolved)
- **Project ID:** `12496218458601315145`
- **Design Systems:**
  - **Celestial Ether** (Light) — asset `8fe8c918253a418db456fc51badcaffe`
  - **SimpleOS Obsidian** (Dark) — asset `fafd2be98b5d434ca0d9ab6c3c5d2598`

### Project B: "SimpleOS Glass" (Original)
- **Project ID:** `14134637940805933672`
- **Design System:** SimpleOS Glass (Dark) — asset `365508527354896466`

---

## 2. Design System Configurations

### 2A. SimpleOS Glass (Original Dark)

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

### 2B. SimpleOS Obsidian (Evolved Dark)

```
displayName: "SimpleOS Obsidian"
colorMode: DARK
headlineFont: SPACE_GROTESK
bodyFont: MANROPE
labelFont: INTER
roundness: ROUND_EIGHT
customColor: "#1A0830"
colorVariant: FIDELITY
overridePrimaryColor: "#F5F5F7"
overrideSecondaryColor: "#1E1E23"
overrideTertiaryColor: "#0F172A"
overrideNeutralColor: "#060612"
```

**Named Colors (Material Design 3 tokens):**

| Token | Hex | Usage |
|-------|-----|-------|
| `surface` | #12121f | Base background |
| `surface_container_lowest` | #0d0d1a | Deepest nested surfaces |
| `surface_container_low` | #1a1a28 | Sidebar backgrounds |
| `surface_container` | #1e1e2c | Standard container |
| `surface_container_high` | #292937 | Cards inside sidebars |
| `surface_container_highest` | #343342 | Hover states, chips |
| `on_surface` | #e3e0f3 | Primary text |
| `on_surface_variant` | #ccc4ce | Secondary text |
| `primary` | #c6c6c8 | Primary actions |
| `primary_container` | #101214 | CTA gradient end |
| `secondary` | #c8c5cc | Supporting interactions |
| `tertiary` | #bec6e0 | Accent tertiary |
| `outline` | #958e98 | Borders (subtle) |
| `outline_variant` | #4a454d | Ghost borders (15% opacity) |
| `error` | #ffb4ab | Error states |

### 2C. Celestial Ether (Light Mode)

```
displayName: "Celestial Ether"
colorMode: LIGHT
headlineFont: SPACE_GROTESK
bodyFont: SPACE_GROTESK
labelFont: SPACE_GROTESK
roundness: ROUND_EIGHT
customColor: "#C8B8E8"
colorVariant: TONAL_SPOT
overridePrimaryColor: "#7C69A3"
overrideSecondaryColor: "#C8B8E8"
overrideNeutralColor: "#F0ECF5"
```

**Named Colors:**

| Token | Hex | Usage |
|-------|-----|-------|
| `surface` | #fcf8ff | Base background |
| `surface_container_lowest` | #ffffff | Frosted glass primary (72% opacity) |
| `surface_container_low` | #f6f2fe | Nested content |
| `surface_container` | #f0ecf9 | Standard container |
| `surface_container_high` | #eae6f5 | Cards |
| `surface_container_highest` | #e4e0f1 | Hover states |
| `on_surface` | #32313e | Primary text (soft, not pure black) |
| `on_surface_variant` | #5f5d6b | Secondary text |
| `primary` | #68558e | Primary actions |
| `primary_container` | #cfb9f9 | CTA gradient end |
| `outline_variant` | #b3b0c0 | Ghost borders |
| `error` | #a8364b | Error states |

---

## 3. Design Language: "The Celestial Architect"

### Core Principles

1. **Every surface is frosted glass** — no flat solid backgrounds
2. **The "No-Line" Rule** — 1px borders are prohibited for section boundaries; use tonal transitions, material shifts, or negative space
3. **Intentional asymmetry** — editorial layout, not grid-locked
4. **Tonal depth over shadows** — stack `surface_container` tiers for hierarchy

### Glass Materials

| Material | Background | Blur | Usage |
|----------|-----------|------|-------|
| **Material A (Active)** | `rgba(30, 30, 35, 0.72)` | 40px | Active windows, primary panels |
| **Material B (Inactive)** | `rgba(15, 23, 42, 0.72)` | 40px | Inactive/background windows |
| **Light Primary** | `rgba(255, 255, 255, 0.72)` | 40px | Light mode windows |
| **Elevated** | `rgba(44, 44, 50, 0.88)` | 40px | Modals, popovers |

### Backgrounds

- **Dark:** Deep space gradient `#060612` (top) to `#1A0830` (bottom)
- **Light:** Lavender gradient `#C8B8E8` (top) to `#F0ECF5` (bottom)

### Borders & Shadows

- **Ghost Border:** `outline_variant` at 15% opacity — felt, not seen
- **Active window shadows:** Multi-layer (9+):
  - Shadow A: `0 24px 48px rgba(0, 0, 0, 0.5)`
  - Shadow B: `0 4px 12px rgba(0, 0, 0, 0.2)`
  - Tint: `on_surface` at 4% opacity for ambient occlusion
- **Inactive:** 3 layers, reduced alpha

### Typography (Tri-Font Strategy)

| Level | Font | Weight | Size | Usage |
|-------|------|--------|------|-------|
| Display | Space Grotesk | 700 | 3.5rem (56px) | OS hero moments, login |
| Headline | Space Grotesk | 500 | 1.75rem (28px) | App headers, window titles |
| Title | Manrope | 600 | 1.125rem (18px) | Section headers |
| Body | Manrope | 400 | 0.875rem (14px) | Content, descriptions |
| Label | Inter | 500 | 0.75rem (12px) | UI controls, buttons |

**Editorial rule:** Space Grotesk = branded/architectural. Manrope = high-density info. Inter = smallest labels only.

### Spacing Scale

```
xs: 4px, sm: 8px, md: 12px, lg: 20px, xl: 32px
```

### Corner Radius

| Element | Radius | Token |
|---------|--------|-------|
| Windows | 12px | `xl` |
| Buttons | 12px | `md` |
| Input fields | 6px | `sm` |
| Dock pill | 26px | custom |
| Full round | 9999px | `full` |

---

## 4. Component Specifications

### Window Chrome

- Title bar: 24-28px, glass surface with blur
- Traffic lights (left): Close #FF5F57, Minimize #FFBD2E, Maximize #28CA41
- Title text: centered, 13px, secondary color
- Internal gutters: 24px, no dividers — use `surface_container_low` for separation

### System Bar (Top, 28px)

- Full-width glass surface, `blur(24px)`
- Left: Logo + active app name + menu items (File, Edit, View, Go, Window)
- Right: Search, Control Center, Wi-Fi, battery %, volume, clock
- Bottom separator: 1px accent-color undertone border

### Dock (Bottom)

- Pill-shaped glass container, 58px tall, 26px corner radius
- Icons: 40px with 48px pill background, 16px gap
- Hover: magnification scale 1.0 to 1.5
- Active indicator: 4px dot below icon
- Apps: Terminal, Files, Calculator, Clock, Settings, Browser, Editor

### Buttons

- **Primary:** Gradient fill `primary` to `primary_container` at 135deg. `label-md` text. Machined-metal feel.
- **Secondary:** Ghost with `surface_container_highest` on hover
- **Tertiary:** Pure typographic, `label-md` styling

### Input Fields

- Background: `surface_container_lowest` with 20% `outline` stroke
- Focus: stroke transitions to `primary`, 2px outer glow at 10% opacity
- Radius: 6px (`sm`)

### Cards & Lists

- NO divider lines — separate with 12px vertical space or hover-state tonal shift
- Cards: `surface_container_high` inside `surface_container_low` parent

### Navigation (Sidebars)

- Active: `primary` vertical pill (4px width) + `surface_container_highest` shift
- Spacing via whitespace, never lines

---

## 5. Interaction States

| State | Effect |
|-------|--------|
| Hover | Border to prominent, shadow upgrade one tier |
| Active/Press | `scale(0.98)` |
| Focus | 3px accent ring at 0.2 alpha |
| Fast transition | 150ms |
| Normal transition | 300ms |
| Easing | `cubic-bezier(0.4, 0.0, 0.2, 1.0)` |

---

## 6. DO's and DON'Ts

### DO
- Use asymmetry — large `display-lg` title offset with small `label-sm` metadata
- Let background bleed through glass — that's the soul of the OS
- Use typography scale aggressively — big headline next to tiny label = editorial
- Use generous padding — if it feels like enough, add 20% more
- Layer glass surfaces — let the gradient glow through

### DON'T
- Use 1px solid borders to define sections (use tonal shifts instead)
- Use flat solid colored backgrounds
- Use sharp corners (minimum 8px radius)
- Use pure black (#000) or pure white (#FFF) — always use tinted neutrals
- Use heavy drop shadows without blur
- Mix rounding types within a component group
- Crowd edges — elements should never feel trapped against container sides
- Forget the gradient background behind all glass layers

---

## 7. Stitch API: Creating a New Theme

### Step 1: Create Project

```
mcp__stitch__create_project(title: "SimpleOS <variant>")
```

### Step 2: Create Design System

Required fields for `create_design_system`:

```json
{
  "projectId": "<project_id>",
  "designSystem": {
    "displayName": "<name>",
    "theme": {
      "colorMode": "DARK | LIGHT",
      "headlineFont": "SPACE_GROTESK | MANROPE | INTER | ...",
      "bodyFont": "MANROPE | INTER | SPACE_GROTESK | ...",
      "labelFont": "INTER | SPACE_GROTESK | ...",
      "roundness": "ROUND_FOUR | ROUND_EIGHT | ROUND_TWELVE | ROUND_FULL",
      "customColor": "#hex",
      "colorVariant": "TONAL_SPOT | FIDELITY | VIBRANT | MONOCHROME | ...",
      "overridePrimaryColor": "#hex (optional)",
      "overrideSecondaryColor": "#hex (optional)",
      "overrideTertiaryColor": "#hex (optional)",
      "overrideNeutralColor": "#hex (optional)",
      "designMd": "<markdown design language — see Section 3>",
      "typography": {
        "display-lg": { "fontFamily": "...", "fontSize": "...", "fontWeight": "...", "lineHeight": "...", "letterSpacing": "..." },
        "body-md": { ... },
        "label-md": { ... }
      },
      "spacing": { "xs": "4px", "sm": "8px", "md": "12px", "lg": "20px", "xl": "32px" }
    }
  }
}
```

### Step 3: Update Design System (activates it)

```
mcp__stitch__update_design_system(name: "assets/<id>", projectId: "<id>", designSystem: { ... })
```

### Step 4: Generate Screens (one at a time, DESKTOP, GEMINI_3_1_PRO)

### Step 5: Apply Design System to Screens

### Step 6: Generate Variants (REFINE/EXPLORE/REIMAGINE)

---

## 8. Available Fonts

```
BE_VIETNAM_PRO, EPILOGUE, INTER, LEXEND, MANROPE, NEWSREADER, NOTO_SERIF,
PLUS_JAKARTA_SANS, PUBLIC_SANS, SPACE_GROTESK, SPLINE_SANS, WORK_SANS,
DOMINE, LIBRE_CASLON_TEXT, EB_GARAMOND, LITERATA, SOURCE_SERIF_FOUR,
MONTSERRAT, METROPOLIS, SOURCE_SANS_THREE, NUNITO_SANS, ARIMO,
HANKEN_GROTESK, RUBIK, GEIST, DM_SANS, IBM_PLEX_SANS, SORA
```

---

## 9. Minimal Screen Set for Full Theme Coverage

When creating a new theme, generate these screens to cover all UI patterns:

| # | Screen | Covers |
|---|--------|--------|
| 1 | **Desktop / Launcher** | System bar, dock, background gradient, desktop icons |
| 2 | **Window Manager (3 windows)** | Window chrome, focus/inactive states, overlapping, shadows |
| 3 | **Settings Panel** | Sidebar navigation, cards, toggles, sliders, nested glass |
| 4 | **File Manager** | Toolbar, sidebar with sections, grid/list views, search, status bar |
| 5 | **Terminal** | Monospace text, syntax highlighting, command prompt, dark content area |
| 6 | **Editor (Code)** | Tab bar, line numbers, syntax colors, minimap, split panes |
| 7 | **Dialog / Modal** | Elevated glass, overlay dimming, button layout, form inputs |
| 8 | **Notification / Toast** | Small floating glass card, icon + text, auto-dismiss |
| 9 | **Login / Lock Screen** | Full-screen gradient, centered glass card, avatar, input field |
| 10 | **Light Mode variant** | Same as #1 or #3 but light theme — validates dual-mode support |

**Minimum viable set:** Screens 1-4 cover 90% of component patterns.
**Full coverage:** All 10 screens ensure every component and interaction state is validated.

---

## 10. Local Code Integration

### Source Files

| File | Purpose |
|------|---------|
| `src/lib/common/ui/glass_tokens.spl` | CSS-text glass token classes (GlassColorTokens, GlassBlurTokens, GlassDesignTokens) |
| `src/lib/common/ui/glass_numeric_tokens.spl` | u64 hex values for baremetal/compositor rendering |
| `src/lib/common/ui/glass_css.spl` | Generates CSS custom properties + component styles from tokens |
| `src/lib/common/ui/glass_theme.spl` | UITheme factory functions (glass_light, glass_dark) |
| `src/lib/common/ui/glass_test_page.spl` | Test page for glass rendering |
| `src/lib/common/ui/design_tokens.spl` | Base iOS token classes (typography, radius, shadow, spacing, animation, opacity) |
| `src/lib/common/ui/ios_theme.spl` | iOS theme presets |
| `src/lib/common/ui/ios_css.spl` | iOS CSS generation |

### Token Sync Rule

The Stitch `designMd` and local `glass_tokens.spl` / `glass_numeric_tokens.spl` must stay in sync:

| Stitch designMd | glass_tokens.spl | glass_numeric_tokens.spl |
|-----------------|-------------------|--------------------------|
| CSS rgba values | GlassColorTokens.dark()/light() | GLASS_DARK_SURFACE, etc. |
| Blur values (CSS px) | GlassBlurTokens.default_blur() | GLASS_BLUR_SURFACE (lower values for 5-pass box blur) |
| Typography | designMd + Stitch typography field | IOSTypographyScale |
| Spacing | designMd + Stitch spacing field | (derived from IOSSpacingScale) |

### Import Path

```simple
use common.ui.glass_tokens.{GlassDesignTokens, GlassColorTokens, GlassBlurTokens}
use common.ui.glass_theme.{glass_light, glass_dark, glass_design_tokens, is_glass_theme}
use common.ui.glass_css.{glass_tokens_to_css, glass_component_css}
use common.ui.glass_numeric_tokens.{GLASS_DARK_BG_TOP, GLASS_DARK_SURFACE, ...}
```

---

## 11. Theme Sharing: GUI Lib + Window Manager

Both the GUI widget library and the window manager compositor consume the same tokens:

- **GUI lib** uses `glass_tokens.spl` (CSS text values) via `glass_css.spl` to generate stylesheets
- **Window manager** uses `glass_numeric_tokens.spl` (u64 hex values) for direct framebuffer/compositor rendering
- **Stitch** uses `designMd` (markdown) to teach Gemini the visual language

To add a new theme variant:
1. Define new color values in both `glass_tokens.spl` (CSS) and `glass_numeric_tokens.spl` (u64)
2. Create a new `UITheme` factory in `glass_theme.spl`
3. Update `designMd` in the Stitch skill or create a new design system via API
4. Generate screens in Stitch to validate visual consistency
5. Apply design system to screens and generate light/dark variants
