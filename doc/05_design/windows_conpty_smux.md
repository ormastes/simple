<!-- codex-design -->
# Windows ConPTY for SMUX Detail Design

The Simple API exposes an opaque integer handle. `open` validates positive
dimensions, `spawn` accepts an explicit program, `platform_default_shell`
selects `COMSPEC`/`cmd.exe` on Windows and `SHELL`/`/bin/sh` on Unix, and
`read`, `write`, and `close` delegate to the raw provider.

SMUX opens once, spawns the platform default shell, routes send/capture through
the Simple API, and closes the handle during shutdown. Failed creation or spawn
keeps the existing scrollback behavior without claiming a PTY exists.
