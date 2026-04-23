# Simple Electron Shell

The Electron shell runs in `electron-ipc` mode. It keeps the Simple subprocess
stdin/stdout transport for desktop builds, while the renderer reuses
`src/app/ui.web/wm.js` for the shared WM frame contract.

Boot contract:

- `index.html` loads the shared `wm.js` bridge.
- `preload.js` exposes `window.simpleUI.onWmFrame` and
  `window.simpleUI.sendFrame` for WebSocket-shaped frames.
- Older Electron IPC messages are routed through
  `simpleWM.receiveElectronMessage(...)`; shared protocol frames are routed
  through `simpleWM.receiveFrame(...)`.
- The renderer does not call `/ui/login` or `/ui/ws` from `file://` contexts.
- Host-window commands render into the main WM surface by default. Set
  `SIMPLE_ELECTRON_HOST_WINDOW_MODE=native` to spawn separate Electron
  `BrowserWindow` instances for diagnostics.
- Native `BrowserWindow` feedback is sent back as `window_cmd` frames with
  `source: "native_event"`.

Commands:

```sh
npm --prefix tools/electron-shell run start -- <entry.spl>
npm --prefix tools/electron-shell run dev -- <entry.spl>
```

Optional advisory host smoke:

```sh
npm --prefix tools/electron-shell ci --no-audit --no-fund
npm --prefix tools/electron-shell run smoke:embedded-host
SIMPLE_ELECTRON_SMOKE=1 npm --prefix tools/electron-shell run smoke:host
```

The smoke exits successfully with a `SKIP:` line when it is not opted in, when
Electron is not installed, or when Linux has no `DISPLAY`/`WAYLAND_DISPLAY` and
`xvfb-run` is unavailable. On headless Linux hosts with `xvfb-run`, the smoke
re-executes itself inside Xvfb, injects `host_window_command` frames through
`wm.js`, and creates a real native `BrowserWindow`.
