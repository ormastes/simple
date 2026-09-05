# Simple WM Modern Preview Evidence - 2026-06-02

## Artifacts
- HTML preview: `build/simple_wm_modern_preview.html`
- Browser screenshot: `build/simple_wm_modern_preview.png`
- Viewport: 1440x900
- Capture command: `npx playwright screenshot --viewport-size=1440,900 --wait-for-timeout=1000 file:///home/ormastes/dev/pub/simple/build/simple_wm_modern_preview.html build/simple_wm_modern_preview.png`

## Result
The delayed browser capture shows the modern WM preview with visible rounded translucent windows, left-top traffic controls, titlebar icon/title/context/input affordances, rounded widgets, the global command palette, and floating rounded taskbar.

The first immediate capture occurred before the opening/restoring animation settled, so the screenshot command now waits 1000ms. A regression contract was added for WM visual layering: the animated desktop background is layer 0, windows are layer 20, taskbar is layer 10000, and command palette is layer 12000.

## Verification
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter` passed 5/5.
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl test/01_unit/app/ui/web_wm_modern_shell_spec.spl` passed.
- `node --check src/app/ui.web/wm.js && node --check src/app/ui.web/retained_renderer.js` passed.
