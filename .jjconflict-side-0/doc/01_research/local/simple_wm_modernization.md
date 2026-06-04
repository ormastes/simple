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
