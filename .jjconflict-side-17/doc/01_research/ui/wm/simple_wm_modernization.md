# Local Research: Simple WM Modernization

Date: 2026-06-02

## Existing WM Surface

- `src/app/ui.web/html.spl` generates the HTML/CSS shell for the Web WM and already owns theme token interpolation, glass colors, traffic-light constants, responsive CSS, widget CSS, and the `#wm-desktop` / `#wm-taskbar` styles.
- `src/app/ui.web/retained_renderer.js` owns retained DOM materialization for server-authoritative surfaces. It creates `.wm-window`, `.wm-titlebar`, traffic-light buttons, `.wm-body`, resize handles, and applies snapshot/patch visibility.
- `src/app/ui.web/wm.js` owns browser transport, taskbar rendering, embedded Electron host windows, drag/resize ghosting, and outbound server-authoritative window commands.
- `src/app/ui.web/taskbar_shell.spl` and `src/app/ui.web/taskbar_runtime_part1.spl` already provide a taskbar model with pinned/running/tray entries and minimized state. No protocol schema change is needed for a first visual modernization slice.

## Implementation Finding

The safest first slice is CSS/DOM lifecycle modernization in the web shell:

- Keep server state authoritative.
- Add lifecycle classes around existing create/remove/visibility paths.
- Add round icon wrappers using existing `icon`, title, app id, or window id fields.
- Keep color and radius theme-driven through generated CSS tokens.
- Add static contract coverage for generated CSS/JS before adding expensive screenshot or QEMU checks.

## Open Local Follow-Up

- Full browser screenshot evidence should be added after the first contract slice.
- Formal color contrast checks are not yet wired for the WM shell.
- Command-bar/browser-address-bar and IDE title-context surfaces need protocol-level or widget-level requirements before deeper implementation.

## 2026-06-04 Codex Addendum: Current Local State

The implementation has advanced beyond the original first slice. Current local evidence:

- `src/app/ui.web/html.spl` now generates a modern WM preview fixture, modern theme CSS aliases (`build_modern_theme_css`, `_wm_css`), effect controls, browser-audit metadata, animated wallpaper tokens, rounded surface tokens, transparency tokens, and Mac-like lifecycle keyframes.
- `src/app/ui.web/wm.js` now contains runtime hooks for window open, close, minimize, restore, maximize, titlebar controls, traffic-light button creation, motion/transparency/feedback preferences, command palette interactions, context menus, widget gallery, window overview, stage rail, dock stack, icon normalization, and quality inspector actions.
- `src/app/ui.web/wm_quality_contract.spl` now checks generated theme CSS, preview HTML, browser-side source markers, color contrast, stable dimensions, material policy, lifecycle motion, reduced/off motion, reduced/off transparency, titlebar command affordances, widgets, icon normalization, and browser-audit readiness.
- `tools/electron-live-bitmap/capture_html_argb.js` now supports optional DOM audit capture through `ELECTRON_CAPTURE_AUDIT_SELECTORS` and `ELECTRON_CAPTURE_AUDIT_OUTPUT`. It records bounds, computed styles, clipping, contrast, touch target checks, contained overlaps, unexpected overlaps, pass/fail state, and failure reasons.
- `test/01_unit/app/ui/web_wm_modern_shell_spec.spl` now acts as the focused executable contract for the Web WM modernization surface. It also generates `doc/06_spec/01_unit/app/ui/web_wm_modern_shell_spec.md`, which now has manual-quality overview, examples, source links, review checklist, expected evidence, and failure triage.

Open local follow-up after the current work:

- Execute the Electron audit command on hosts with Electron/Xvfb installed and store representative JSON/PNG artifacts under a stable evidence path.
- Convert the audit JSON pass/fail into a dedicated integration/system test once host dependencies and baseline policy are stable.
- Decide whether browser/IDE titlebar command semantics need protocol-level state beyond the current generated preview/runtime affordances.
- Decide whether round-icon conversion should remain CSS/runtime normalization or add bitmap preprocessing for imported square icons.
- Extend comparable quality gates to native/QEMU SimpleOS WM paths after the Web WM contract remains stable.
