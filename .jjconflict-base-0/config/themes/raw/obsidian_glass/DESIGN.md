---
name: Obsidian Glass
colors:
  surface: '#131313'
  surface-dim: '#131313'
  surface-bright: '#3a3939'
  surface-container-lowest: '#0e0e0e'
  surface-container-low: '#1c1b1b'
  surface-container: '#201f1f'
  surface-container-high: '#2a2a2a'
  surface-container-highest: '#353534'
  on-surface: '#e5e2e1'
  on-surface-variant: '#c4c7c8'
  inverse-surface: '#e5e2e1'
  inverse-on-surface: '#313030'
  outline: '#8e9192'
  outline-variant: '#444748'
  surface-tint: '#c6c6c7'
  primary: '#ffffff'
  on-primary: '#2f3131'
  primary-container: '#e2e2e2'
  on-primary-container: '#636565'
  inverse-primary: '#5d5f5f'
  secondary: '#adc6ff'
  on-secondary: '#002e6a'
  secondary-container: '#0566d9'
  on-secondary-container: '#e6ecff'
  tertiary: '#ffffff'
  on-tertiary: '#2f3131'
  tertiary-container: '#e2e2e2'
  on-tertiary-container: '#636565'
  error: '#ffb4ab'
  on-error: '#690005'
  error-container: '#93000a'
  on-error-container: '#ffdad6'
  primary-fixed: '#e2e2e2'
  primary-fixed-dim: '#c6c6c7'
  on-primary-fixed: '#1a1c1c'
  on-primary-fixed-variant: '#454747'
  secondary-fixed: '#d8e2ff'
  secondary-fixed-dim: '#adc6ff'
  on-secondary-fixed: '#001a42'
  on-secondary-fixed-variant: '#004395'
  tertiary-fixed: '#e2e2e2'
  tertiary-fixed-dim: '#c6c6c7'
  on-tertiary-fixed: '#1a1c1c'
  on-tertiary-fixed-variant: '#454747'
  background: '#131313'
  on-background: '#e5e2e1'
  surface-variant: '#353534'
typography:
  headline-xl:
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
    letterSpacing: -0.01em
  body-lg:
    fontFamily: Inter
    fontSize: 18px
    fontWeight: '400'
    lineHeight: '1.6'
    letterSpacing: 0em
  body-md:
    fontFamily: Inter
    fontSize: 16px
    fontWeight: '400'
    lineHeight: '1.6'
    letterSpacing: 0em
  body-sm:
    fontFamily: Inter
    fontSize: 14px
    fontWeight: '400'
    lineHeight: '1.5'
    letterSpacing: 0em
  label-md:
    fontFamily: Inter
    fontSize: 12px
    fontWeight: '600'
    lineHeight: '1'
    letterSpacing: 0.05em
  label-sm:
    fontFamily: Inter
    fontSize: 10px
    fontWeight: '700'
    lineHeight: '1'
    letterSpacing: 0.08em
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
  xl: 48px
  xxl: 80px
  container-max: 1440px
  gutter: 24px
---

## Brand & Style

This design system is built upon the principles of **Precision Minimalism** and **Advanced Glassmorphism**. It evokes the sensation of high-end hardware interfaces—specifically, the interplay between polished obsidian surfaces and precision-milled aluminum. 

The aesthetic is "water-clear," focusing on optical clarity, depth without clutter, and a sophisticated technological aura. It targets professional environments where focus, premium quality, and institutional trust are paramount. The emotional response is one of calm, controlled power and absolute clarity.

## Colors

The palette is anchored in "Pure Dark" tones. To avoid a "muddy" appearance, the base neutrals use a hint of cool slate rather than warm brown undertones. 

*   **Primary:** A stark, clinical White (#FFFFFF) used for high-contrast typography and essential icons.
*   **Secondary:** A vibrant, digital Blue (#3B82F6) reserved for active states and critical calls to action.
*   **Neutrals:** The background is a near-black (#050505), with surfaces stepping up to a rich charcoal (#0A0A0B). 
*   **Accents:** Translucency is the primary "color" tool, using varying levels of white alpha transparency to create depth rather than introducing new hex codes.

## Typography

This design system utilizes a dual-font strategy to balance character with utility. **Manrope** provides a modern, geometric structure for headlines, appearing sharp and intentional. **Inter** handles all functional and body text, ensuring maximum legibility across high-density data and interface controls.

All type should be rendered with `antialiased` smoothing. Use pure white for primary content and 60% white (RGBA) for secondary descriptions to maintain the hierarchy without introducing muddy greys.

## Layout & Spacing

The layout follows a strict 4px baseline grid. Content is organized within a 12-column fluid system with generous gutters to maintain a sense of "air." 

Elements should be grouped with tight internal spacing (4px/8px) but separated from other groups with significant negative space (48px+). This creates a "cluster" effect typical of sophisticated instrument panels, where focus is directed to specific functional zones.

## Elevation & Depth

Depth is not communicated through shadows, but through **Optical Translucency**. 

1.  **The Base:** The bottom-most layer is the deep neutral background.
2.  **The Glass:** Floating panels utilize a `backdrop-filter: blur(20px)` and a background color of `rgba(255, 255, 255, 0.03)`.
3.  **The Border:** Every floating element must have a 1px solid border. The border is a top-to-bottom linear gradient: `rgba(255, 255, 255, 0.2)` to `rgba(255, 255, 255, 0.05)`.
4.  **The Glow:** Apply an `inset` box shadow of 1px 1px 2px `rgba(255, 255, 255, 0.1)` to simulate light hitting the edge of a glass pane.

## Shapes

The shape language is "Rounded-Technical." We move away from aggressive sharp corners in favor of substantial, deliberate radii that soften the high-tech aesthetic, making the interface feel more approachable and ergonomic.

Standard components (buttons, inputs) use an 8px radius. Larger containers and cards use a 16px or 24px radius. This maintains the premium hardware feel—reminiscent of high-end consumer electronics with smooth, continuous industrial curves—while ensuring the "glass" panels feel like finished, tactile objects.

## Components

### Buttons
Primary buttons are solid White with Black text. Secondary buttons are transparent glass panes with white borders. The hover state should increase the `backdrop-filter` intensity rather than changing the background color significantly. All buttons use a base 8px corner radius.

### Input Fields
Inputs should be completely transparent with a 1px bottom border of `rgba(255, 255, 255, 0.3)`. On focus, the border should glow with a subtle outer bloom of the secondary blue.

### Cards & Panels
Cards must use the glassmorphism stack: 20px blur, thin white border gradient, and subtle inner glow. Containers utilize the "Rounded" shape logic with 16px+ radii to define the layout.

### Chips & Tags
Small, pill-shaped glass elements with high-transparency backgrounds. Labels inside chips should always be in the `label-sm` typographic style.

### System Indicators
Use high-clarity status dots (8px circles) with a slight "pulse" animation for active processes. These are the only elements allowed to use saturated colors (Green for success, Red for error) but they should be kept small and luminous.