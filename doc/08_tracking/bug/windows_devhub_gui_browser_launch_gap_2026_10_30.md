# Windows DevHub browser-shell launch gap (2026-10-30)

## Observation

Static inspection of `src/app/devhub/gui_server.spl` shows that the browser
shell searches only for `/usr/bin/open` and `/usr/bin/xdg-open` (lines 27–31).
When neither path exists, `_devhub_gui_open` prints a manual-open message and
returns `false` (lines 32–34). `run_devhub_gui` then closes the listener and
returns failure when that result is false (lines 114–116). Windows hosts
normally do not expose either Unix path, so the default browser-shell launch
has no Windows opener in this code path.

The shared `src/lib/nogc_sync_mut/desktop/shell_open.spl` implementation also
does not currently supply one: `open_url` handles Linux and macOS only and
returns `NotSupported` for other platforms (lines 13–23). Calling that helper
alone would therefore not close the Windows gap.

This is a source-level launch gap, not a reproduced runtime failure. No native
DevHub GUI launch has yet been attempted on Windows for this report.

## Owner direction

Add a Windows-capable URL-opening provider to the shared desktop shell API and
route DevHub browser-shell launches through it, or add an equivalent shared
Windows provider. Keep the loopback server available and print its URL if the
browser cannot be opened. The Electron shell is a separate existing route and
does not establish browser-shell behavior.

## Unblock evidence

On a Windows host, launch a native-built DevHub with `--gui --port <port>` in
browser mode. Confirm the browser opens the loopback page, `/api/status`
returns the ready record, and the server remains alive. Also exercise the
documented open-failure path to confirm the URL remains usable manually. Do
not close this item based only on the Electron-shell launch or static checks.
