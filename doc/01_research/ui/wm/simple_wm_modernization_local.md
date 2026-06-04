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

## 2026-06-04 Codex Addendum: Current Primary-Source Guidance

Sources consulted:

- Apple Human Interface Guidelines, Materials: https://developer.apple.com/design/Human-Interface-Guidelines/materials
- Apple Support, Customize onscreen motion on Mac: https://support.apple.com/guide/mac-help/mchlc03f57a1/mac
- W3C WCAG 2.2: https://www.w3.org/TR/WCAG22/
- W3C Understanding SC 1.4.3 Contrast Minimum: https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum
- Material Design, Motion: https://m1.material.io/motion/material-motion.html
- Material Design, Duration and easing: https://m1.material.io/motion/duration-easing.html

Findings to carry into Simple WM:

- Materials should be semantic and contextual, not random glass. Apple guidance favors system-style materials/vibrancy where translucency improves communication, and it emphasizes testing in varied contexts. Simple WM should keep transparency behind material policy tokens and must preserve reduced/off transparency modes.
- Reduced motion is an accessibility feature, not only a preference. macOS exposes Reduce Motion for opening apps, switching spaces, and opening/closing UI surfaces. Simple WM should keep lifecycle animations optional and make reduced/off paths easy to audit.
- Motion should communicate organization, hierarchy, gesture result, and focus. Material guidance frames motion as responsive, natural, aware, and intentional. Simple WM should animate window open/close/minimize/restore, focus changes, command palette selection, widget feedback, and wallpaper drift only when these clarify state.
- Desktop durations should stay short. Material guidance places desktop animations around the 150-200 ms range, with longer durations only for larger travel or surface transformation. The existing Simple WM values of close 180 ms, minimize 210 ms, and reduced open 120 ms align with this; open 260 ms should remain justified by spring-style creation and should be reduced/off by policy.
- Color quality should use computed foreground/background values. WCAG explains that contrast checks should use user-agent/stylesheet colors instead of anti-aliased pixels and that 4.5:1 is a threshold, not a rounded target. Simple WM should keep `contrast_ratio_x100 >= 450` as the AA baseline and report exact computed ratios.
- Target-size quality should use WCAG 2.2 as the accessibility baseline. WCAG 2.2 adds target-size minimum guidance, so Simple WM should keep 44 px touch targets as a stronger shell-level policy while the browser audit records actual interactive element dimensions.
- Visual QA should separate intended containment from defects. Window shells contain titlebars, buttons, and content by design; the audit should treat parent-child overlap separately from unexpected sibling/cross-surface overlap.

Recommended next feature set:

1. Keep modern motion focused on lifecycle, focus, command, widget, and spatial transitions.
2. Keep material/transparency policy controlled by root data attributes and reflected in the preview fixture.
3. Keep browser-audit evidence as a pass/fail gate with contrast, touch, clipping, and unexpected-overlap failures.
4. Add real capture execution where host dependencies are available, but keep static command/report coverage so CI without Electron can still verify the contract.
5. Treat any new decorative animation as suspect unless it communicates state or has a visible off/reduced path.
