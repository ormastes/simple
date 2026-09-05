---
name: Aetheric OS
colors:
  surface: '#131315'
  surface-dim: '#131315'
  surface-bright: '#39393b'
  surface-container-lowest: '#0e0e10'
  surface-container-low: '#1b1b1d'
  surface-container: '#1f1f21'
  surface-container-high: '#2a2a2c'
  surface-container-highest: '#353437'
  on-surface: '#e4e2e4'
  on-surface-variant: '#c1c6d7'
  inverse-surface: '#e4e2e4'
  inverse-on-surface: '#303032'
  outline: '#8b90a0'
  outline-variant: '#414755'
  surface-tint: '#adc6ff'
  primary: '#adc6ff'
  on-primary: '#002e69'
  primary-container: '#4b8eff'
  on-primary-container: '#00285c'
  inverse-primary: '#005bc1'
  secondary: '#c2c1ff'
  on-secondary: '#1800a7'
  secondary-container: '#3630bf'
  on-secondary-container: '#b1b1ff'
  tertiary: '#e9b3ff'
  on-tertiary: '#510074'
  tertiary-container: '#c863fb'
  on-tertiary-container: '#460066'
  error: '#ffb4ab'
  on-error: '#690005'
  error-container: '#93000a'
  on-error-container: '#ffdad6'
  primary-fixed: '#d8e2ff'
  primary-fixed-dim: '#adc6ff'
  on-primary-fixed: '#001a41'
  on-primary-fixed-variant: '#004493'
  secondary-fixed: '#e2dfff'
  secondary-fixed-dim: '#c2c1ff'
  on-secondary-fixed: '#0c006b'
  on-secondary-fixed-variant: '#332dbc'
  tertiary-fixed: '#f6d9ff'
  tertiary-fixed-dim: '#e9b3ff'
  on-tertiary-fixed: '#310048'
  on-tertiary-fixed-variant: '#7200a3'
  background: '#131315'
  on-background: '#e4e2e4'
  surface-variant: '#353437'
typography:
  display-lg:
    fontFamily: Manrope
    fontSize: 48px
    fontWeight: '700'
    lineHeight: '1.1'
    letterSpacing: -0.02em
  headline-lg:
    fontFamily: Manrope
    fontSize: 32px
    fontWeight: '600'
    lineHeight: '1.2'
    letterSpacing: -0.01em
  headline-md:
    fontFamily: Manrope
    fontSize: 24px
    fontWeight: '600'
    lineHeight: '1.3'
  body-lg:
    fontFamily: Inter
    fontSize: 18px
    fontWeight: '400'
    lineHeight: '1.5'
  body-md:
    fontFamily: Inter
    fontSize: 16px
    fontWeight: '400'
    lineHeight: '1.5'
  label-md:
    fontFamily: Inter
    fontSize: 14px
    fontWeight: '500'
    lineHeight: '1.2'
    letterSpacing: 0.01em
  label-sm:
    fontFamily: Inter
    fontSize: 12px
    fontWeight: '600'
    lineHeight: '1.2'
    letterSpacing: 0.03em
rounded:
  sm: 0.25rem
  DEFAULT: 0.5rem
  md: 0.75rem
  lg: 1rem
  xl: 1.5rem
  full: 9999px
spacing:
  unit: 4px
  xs: 4px
  sm: 8px
  md: 16px
  lg: 24px
  xl: 40px
  gutter: 20px
  margin: 32px
---

## Brand & Style

The design system is engineered to evoke the feeling of a high-end desktop operating system. It prioritizes depth, immersion, and precision. The target audience includes power users, creative professionals, and tech enthusiasts who value an aesthetic that feels both futuristic and grounded.

The style is a sophisticated blend of **Glassmorphism** and **Minimalism**. It leverages high-quality background blurs (20px to 40px) to create a sense of physical space. Surfaces are not merely flat colors but are treated as "materials" that react to the content beneath them. Subtle inner glows and micro-borders simulate light refracting through the edges of glass panels, ensuring elements remain distinct even within a dark, low-contrast environment.

## Colors

The palette is rooted in deep obsidian grays and midnight blues to minimize eye strain and maximize the impact of translucent effects. 

- **Primary**: A vibrant sapphire blue used for active states, primary actions, and focus indicators.
- **Secondary**: A deep violet used for accented information and secondary interactive elements.
- **Surface**: The foundation is a rich charcoal (#1C1C1E) with varying levels of opacity (from 70% to 90%) to allow background colors to bleed through.
- **Accents**: Subtle glows use the primary color with a 15-20% opacity to create "light pools" around high-priority containers.

## Typography

This design system utilizes a dual-font approach to balance character with utility. **Manrope** provides a modern, geometric feel for headlines, offering a slight personality that distinguishes the UI from standard enterprise tools. **Inter** is used for all functional text, body copy, and UI labels due to its exceptional legibility at small sizes and high x-height.

Weight is used strategically: headlines use Semi-Bold and Bold to anchor the layout, while body text remains in Regular or Medium to maintain a clean, airy aesthetic against dark backgrounds.

## Layout & Spacing

The layout philosophy follows a **Fluid Grid** model with generous safe areas. A 12-column system is used for primary content, while utility panels (sidebars, inspectors) use fixed widths (e.g., 260px) to mimic desktop app behavior.

The spacing rhythm is built on a 4px baseline. Components and containers should favor larger internal padding to reinforce the "premium" feel. Layouts should utilize "negative space" as a functional element, allowing the glass effects and background blurs to provide a sense of breathing room.

## Elevation & Depth

Depth is the defining characteristic of this design system. It is achieved through three specific layers:

1.  **The Background**: A dynamic mesh gradient or wallpaper that sits at the lowest level.
2.  **The Frost**: Semi-transparent containers with a `backdrop-filter: blur(30px)`. These panels have a 0.5px white border at 15% opacity to define their edges.
3.  **The Glow**: Active or elevated elements (like modal windows) feature an "ambient shadow"—a very large, soft shadow (60px blur) with a hint of the primary blue color at 10% opacity, rather than pure black.

Stacking is handled through increasing the opacity of the surface color; the higher the element, the more opaque its "glass" becomes.

## Shapes

The design system employs a **Rounded** shape language to feel approachable and organic. The base corner radius is 8px (0.5rem), which scales up to 16px (1rem) for standard cards and 24px (1.5rem) for main window frames.

This consistency in curvature mirrors the hardware aesthetics of modern premium laptops and displays. Buttons should always match the radius of their parent container's inner padding to maintain visual harmony (the "concentric circles" effect).

## Components

- **Buttons**: Primary buttons are solid vibrant blue with a subtle top-down gradient. Secondary buttons are "glass" with a 1px border. Hover states should trigger a subtle inner glow.
- **Input Fields**: Backgrounds should be slightly darker than the surface they sit on, with a subtle 1px bottom border that highlights in the primary color upon focus.
- **Cards/Windows**: Every card is a glass panel. They must include a "light leak" effect—a subtle linear gradient from the top-left corner to simulate a physical light source.
- **Lists/Menus**: Selection states in lists should use a rounded "pill" highlight in the primary color with 20% opacity, ensuring the text remains legible while the background blur is still visible.
- **Checkboxes & Radios**: These should be treated as "miniature glass" elements. When checked, they fill with the primary color and emit a small, soft glow.
- **Progress Bars**: Use a translucent track with a glowing, high-saturation blue fill.