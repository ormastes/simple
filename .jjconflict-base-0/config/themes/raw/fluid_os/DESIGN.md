---
name: Fluid OS
colors:
  surface: '#faf9fe'
  surface-dim: '#dad9df'
  surface-bright: '#faf9fe'
  surface-container-lowest: '#ffffff'
  surface-container-low: '#f4f3f8'
  surface-container: '#eeedf3'
  surface-container-high: '#e9e7ed'
  surface-container-highest: '#e3e2e7'
  on-surface: '#1a1b1f'
  on-surface-variant: '#414755'
  inverse-surface: '#2f3034'
  inverse-on-surface: '#f1f0f5'
  outline: '#717786'
  outline-variant: '#c1c6d7'
  surface-tint: '#005bc1'
  primary: '#0058bc'
  on-primary: '#ffffff'
  primary-container: '#0070eb'
  on-primary-container: '#fefcff'
  inverse-primary: '#adc6ff'
  secondary: '#006687'
  on-secondary: '#ffffff'
  secondary-container: '#60cdff'
  on-secondary-container: '#005572'
  tertiary: '#8a2bb9'
  on-tertiary: '#ffffff'
  tertiary-container: '#a649d5'
  on-tertiary-container: '#fffbff'
  error: '#ba1a1a'
  on-error: '#ffffff'
  error-container: '#ffdad6'
  on-error-container: '#93000a'
  primary-fixed: '#d8e2ff'
  primary-fixed-dim: '#adc6ff'
  on-primary-fixed: '#001a41'
  on-primary-fixed-variant: '#004493'
  secondary-fixed: '#c1e8ff'
  secondary-fixed-dim: '#74d1ff'
  on-secondary-fixed: '#001e2b'
  on-secondary-fixed-variant: '#004d67'
  tertiary-fixed: '#f6d9ff'
  tertiary-fixed-dim: '#e8b3ff'
  on-tertiary-fixed: '#310048'
  on-tertiary-fixed-variant: '#7201a2'
  background: '#faf9fe'
  on-background: '#1a1b1f'
  surface-variant: '#e3e2e7'
typography:
  headline-xl:
    fontFamily: Plus Jakarta Sans
    fontSize: 48px
    fontWeight: '700'
    lineHeight: '1.1'
    letterSpacing: -0.02em
  headline-lg:
    fontFamily: Plus Jakarta Sans
    fontSize: 32px
    fontWeight: '600'
    lineHeight: '1.2'
    letterSpacing: -0.01em
  headline-md:
    fontFamily: Plus Jakarta Sans
    fontSize: 24px
    fontWeight: '600'
    lineHeight: '1.3'
  body-lg:
    fontFamily: Inter
    fontSize: 18px
    fontWeight: '400'
    lineHeight: '1.6'
  body-md:
    fontFamily: Inter
    fontSize: 16px
    fontWeight: '400'
    lineHeight: '1.5'
  body-sm:
    fontFamily: Inter
    fontSize: 14px
    fontWeight: '400'
    lineHeight: '1.4'
  label-lg:
    fontFamily: Inter
    fontSize: 14px
    fontWeight: '600'
    lineHeight: '1'
    letterSpacing: 0.02em
  label-sm:
    fontFamily: Inter
    fontSize: 12px
    fontWeight: '500'
    lineHeight: '1'
    letterSpacing: 0.04em
rounded:
  sm: 0.25rem
  DEFAULT: 0.5rem
  md: 0.75rem
  lg: 1rem
  xl: 1.5rem
  full: 9999px
spacing:
  unit: 8px
  gutter: 24px
  margin: 32px
  container-padding: 1.5rem
  stack-gap: 1rem
---

## Brand & Style
The design system is centered around the concept of "Hydro-Minimalism." It seeks to evoke the sensory experience of water: its clarity, its effortless flow, and its refreshing presence. The target audience is users who seek a calm, undistracted digital environment that feels breathable and alive.

The style is a sophisticated blend of **Glassmorphism** and **Minimalism**. It prioritizes high-transparency layers, caustic-inspired gradients, and significant whitespace to simulate the airiness of a light-filled aquatic environment. UI elements should feel like they are suspended in a clear medium rather than anchored to a static grid, utilizing motion and depth to guide the user’s eye.

## Colors
This design system utilizes a palette of "Hydrated Primaries." The core is a spectrum of blues and cyans that represent different depths of water. 

- **Primary:** A vibrant "Cerulean Blue" used for interactive states and key brand moments.
- **Secondary:** A "Glacier Teal" for supplementary information and soft highlights.
- **Tertiary:** A "Deep Orchid" used sparingly for high-contrast alerts or unique notification types.
- **Surface Colors:** Pure white (#FFFFFF) is used only for the most elevated elements. Lower-tier surfaces use a "Mist White" (#F2F7FF) to maintain a cool temperature across the UI.
- **Gradients:** Use linear gradients with 15% opacity shifts to mimic light refracting through liquid.

## Typography
The typography strategy balances character with utility. **Plus Jakarta Sans** is used for headlines to provide a soft, organic feel that complements the fluid UI shapes. Its modern, slightly wide apertures feel welcoming and fresh.

For the functional "heavy lifting," **Inter** is utilized. It provides the crispness required for an OS, ensuring that even at small sizes (labels and system metadata), information remains highly legible. Line heights are intentionally generous to reinforce the "airy" brand pillar, preventing the UI from feeling cramped or dense.

## Layout & Spacing
The layout follows a **Fluid Grid** philosophy. Content should expand naturally to fill the viewport, but with significant internal "breathing room." The design system uses an 8px base unit to maintain a rhythmic spacing scale.

Margins and gutters are wider than industry standards to emphasize clarity. Elements are grouped into "Pools" (containers) that use dynamic padding based on the screen size. Use "Float" alignment—avoiding harsh edge-to-edge containers where possible—to make the UI feel like it is gently drifting on the screen.

## Elevation & Depth
Elevation in this design system is achieved through **Glassmorphism** and **Ambient Shadows**. Instead of traditional solid shadows, we use "diffused caustic shadows."

- **Backdrop Blur:** All elevated containers must use a `backdrop-filter: blur(20px)` combined with a 70-80% opacity white fill. This simulates looking through frosted glass or clear water.
- **Shadows:** Shadows are highly diffused (large blur radius) and carry a 2% blue tint (#0044FF at 5% opacity) to prevent the "muddy" look of neutral grey shadows.
- **Z-Axis Layers:**
  - *Layer 1 (Bottom):* The fluid background gradient.
  - *Layer 2 (Content):* Glass cards with subtle 1px white internal borders.
  - *Layer 3 (Top):* Interactive elements (buttons, toggles) with higher contrast and sharper shadows.

## Shapes
The shape language is organic and soft. Standard containers use a **Rounded** (Level 2) corner radius to avoid the harshness of sharp corners while maintaining professional structure.

Interactive components like buttons and search bars should utilize **Pill-shaped** (Level 3) radii to mimic the smoothness of river stones. The interaction of these rounded forms creates a "liquid" aesthetic when elements are stacked or nested. Avoid any 0px corners; every edge in the design system should feel safe and polished.

## Components
- **Buttons:** Primary buttons use a subtle "liquid" gradient (Secondary Color to Primary Color). They feature a 1px "inner glow" border at the top to simulate light hitting a surface.
- **Chips:** Highly transparent, pill-shaped tags with a 1px border. On hover, the opacity increases slightly, as if the chip is becoming more "solid."
- **Cards:** Glass-morphic surfaces with a 24px corner radius. They should not have heavy shadows; instead, use a 1px white stroke at 20% opacity to define the edge against the background.
- **Input Fields:** Soft-filled containers (#F2F7FF) that transition to a crisp white with a blue glow when focused. 
- **Checkboxes & Radios:** These should feel "squishy." Use a slight scale-down animation (0.95x) when clicked, followed by a bounce back to 1.0x to emphasize the fluid nature of the system.
- **Additional Suggestion - The "Droplet" Indicator:** For notifications or active states, use a small, glowing circular indicator with a pulse animation to mimic a ripple effect.