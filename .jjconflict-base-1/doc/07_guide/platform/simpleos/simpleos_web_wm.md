# SimpleOS Web WM Guide

The SimpleOS Web WM is the browser-hosted runtime for the SimpleOS desktop
shell. It serves a themed desktop page over HTTP and drives windows through a
WebSocket message stream.

Current runtime identity:

- page title: `SimpleOS Web WM`
- fixture: `examples/06_io/ui/simpleos_web_wm.ui.sdn`
- canonical theme: `aetheric_dark` (`glass_obsidian_dark` is a compatibility alias)
- default window set: `Terminal`, `Editor`, `Browser`, `File Manager`

---

## Entrypoint

The standard entry is:

- [examples/06_io/ui/web_wm.spl](../../../../examples/06_io/ui/web_wm.spl)

That entry routes into:

- [src/app/ui.web/server.spl](../../../../src/app/ui.web/server.spl)
- [src/app/ui.web/html.spl](../../../../src/app/ui.web/html.spl)
- [src/app/ui.web/ws_handler.spl](../../../../src/app/ui.web/ws_handler.spl)

---

## Runtime Model

The browser client loads:

- `/` for the HTML shell
- `/ws` for the live WM message stream

The HTML shell embeds:

- theme CSS from `generate_css(theme)`
- the WM implementation from `src/app/ui.web/wm.js`
- a generated boot script from `generate_wm_js(ws_port)`

The server upgrades `/ws` to a WebSocket and pushes WM messages such as
`openWindow` into the browser.

---

## First-Load Behavior

The WM is expected to render on the first page load from a clean server start.

The current boot script explicitly handles two failure modes:

- the page script running after `DOMContentLoaded` has already fired
- a socket stuck in `CONNECTING` without ever reaching `OPEN`

`generate_wm_js()` now:

- boots immediately when `document.readyState` is already past `loading`
- adds an `onerror` path
- adds a connect timeout for sockets stuck in `readyState === 0`
- schedules reconnects without opening duplicate live sockets

Expected runtime truth for a healthy first load:

- title `SimpleOS Web WM`
- 4 windows visible
- 4 taskbar items visible
- console contains `WM WebSocket connected`

---

## Theme Path

The package/snapshot model is the sole Web WM visual authority. The repaired
canonical adapter retains structural layout and interaction selectors while
Aetheric package CSS owns paint and material values. Source review is accepted;
live parser/Draw-IR/pixel/event evidence remains **RUNTIME UNVERIFIED**. See the
[dated verification handoff](../../../08_tracking/bug/web_css_package_authority_adapter_2026-07-27.md).

Theme flow:

1. `config/themes/theme.sdn` selects `aetheric_dark`; legacy Glass/Obsidian
   IDs resolve through its alias table.
2. `nogc_sync_mut.ui.theme_package` resolves the family/package CSS and icons,
   then creates the immutable `ThemeRenderSnapshot`.
3. `src/app/ui.web/html.spl::generate_css()` consumes the resolved package CSS.
   The adapter supplies structure and package-variable references, not a second
   visual authority.
4. Simple Web app-window HTML is wrapped by
   `src/os/compositor/simple_web_window_renderer.spl` with the same generated CSS
5. `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` applies embedded
   `<style>` blocks and resolves CSS variables before pixel rendering
6. The HTML layout renderer records canonical CPU/solid material entries from
   loop-local computed style before the freestanding `[Style]` array boundary;
   animated material nodes remain unverified and therefore emit no receipt.

For the full production theme workflow, see
[stitch_simple_os_theme.md](../../ui/stitch_simple_os_theme.md). The legacy
numeric/text Glass tokens and `GlassConfig` presets are compatibility APIs,
not this runtime's theme-authoring authority.

The active WM glass implementation and evidence boundaries are documented in
[the architecture/detail design](../../../05_design/wm_glass_theme_host_simpleos.md),
[system-test plan](../../../03_plan/sys_test/wm_glass_theme_host_simpleos.md),
and [agent plan](../../../03_plan/agent_tasks/wm_glass_theme_host_simpleos.md).

---

## Running It

The practical runtime path today is source execution:

```bash
bin/simple run examples/06_io/ui/web_wm.spl
```

Use an admitted self-hosted `bin/simple`; the Rust bootstrap seed is not a
product runner or acceptable evidence source.

Then open:

```text
http://localhost:3333/
```

### Current compile-path caveat

Direct compile of examples that import the web backend is still not fully
closed. The compile-time resolver now finds the dotted backend path
(`app.ui.web.server` from `src/app/ui.web/server.spl`), but direct compile
still fails one level deeper on transitive backend imports during semantic
resolution.

Current result:

- source execution launches the server
- direct compile no longer stops at `run_web` / `run_web_wm`
- direct compile still fails on transitive imports such as
  `app.io.env_ops.{env_get}` with `undefined identifier: env_get`

This is still a compiler/import-resolution issue, not a missing function in
`src/app/ui.web/server.spl`.

---

## Verification Checklist

Use this when checking the live browser runtime:

1. Start the server from a clean process.
2. Open `http://localhost:3333/`.
3. Confirm the title is `SimpleOS Web WM`.
4. Confirm the desktop shows 4 windows.
5. Confirm the taskbar shows 4 entries.
6. Confirm taskbar click/focus/minimize/restore behavior.
7. Check the browser console for `WM WebSocket connected`.

Expected non-fatal noise:

- favicon `404`

---

## Related Tooling

- [app/ui/wm_compare.md](../../app/ui/wm_compare.md)
- [app/ui/wm_ui_snapshot.md](../../app/ui/wm_ui_snapshot.md)
- [platform/simpleos_dev_guide.md](simpleos_dev_guide.md)
