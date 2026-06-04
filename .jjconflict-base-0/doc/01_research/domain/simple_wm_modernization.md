# Domain Research: Simple WM Modernization

Date: 2026-06-02

## Sources Consulted

- Apple Human Interface Guidelines, Motion: https://developer.apple.com/design/human-interface-guidelines/motion
- Material Design 3, Motion overview: https://m3.material.io/styles/motion/overview
- Fluent 2, Color: https://fluent2.microsoft.design/color
- Fluent 2, Layout: https://fluent2.microsoft.design/layout

## Findings Applied

- Motion should communicate state changes, not decorate every element. The first implementation applies motion only to WM lifecycle states: open, close, minimize, restore, focus/taskbar hover, and background drift.
- Reduced-motion support is mandatory for modern UI quality. The WM CSS now includes a `prefers-reduced-motion: reduce` override for window/background/taskbar motion.
- Color should use semantic/design tokens instead of scattered literals. The first slice keeps WM shell colors inside `generate_css` token interpolation and existing traffic-light constants.
- Layout quality depends on stable spacing/radius dimensions. The first slice uses fixed icon/taskbar/control dimensions, text truncation, and existing radius variables so labels and icons do not resize the shell.

## Next Research Questions

- Decide whether Simple WM wants a dock-like taskbar, command-bar-first shell, or IDE/browser hybrid titlebar as the primary OS experience.
- Add screenshot-based checks for contrast, layout overlap, text fit, and animation class behavior.
- Define requirements for square-to-round icon conversion beyond CSS clipping if actual bitmap normalization is required.
