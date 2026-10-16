<!-- codex-design -->
# Windows ConPTY for SMUX Detail Design

The Simple API exposes an opaque integer handle. `open` validates positive
dimensions, `spawn` accepts an explicit program, `platform_default_shell`
selects `COMSPEC`/`cmd.exe` on Windows and `SHELL`/`/bin/sh` on Unix, and
`read`, `write`, and `close` delegate to the raw provider.

SMUX opens once, spawns the platform default shell, routes send/capture through
the Simple API, and closes the handle during shutdown. Failed creation or spawn
keeps the existing scrollback behavior without claiming a PTY exists.

## Windows service corrections, 2026-10-16

The production service uses `os.apps.smux.layout.smux_plan_split` for pane
geometry. `vertical`/`v` divides columns; `horizontal`/`h` divides rows. One
cell is reserved for the separator. Both regions must have at least one cell.
Validation and capacity checks precede the single service-state commit; a
rejected split consumes neither a pane slot nor an id. Child spawn remains
explicit, as required by the service API.

Resize refuses nonpositive dimensions before updating geometry or metrics.
This describes service geometry only: notifying a running ConPTY child still
requires a PTY resize provider and runtime evidence.

Client attachment refuses unknown sessions, empty client ids, nonpositive
dimensions, and new clients beyond the four-client table. Refusal uses the
existing `MuxClientAttachment.attached = false` result. Reattaching an existing
client updates its session and dimensions without requiring a free slot;
unrelated client records survive the replacement.

The direct-service SSpec is
`test/03_system/tools/smux_service_features_spec.spl`. It exercises the
production API rather than a local session registry. In-process detach
evidence cannot establish survival after the client process exits. The hosted
line protocol currently owns and shuts down its service; cross-process
detach/reconnect remains an outstanding architecture gap.
