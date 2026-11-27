# SimpleOS PTY provider: unverified on QEMU real firmware and board

Status: open (2026-11-14)

`src/os/apps/shell/pty_provider.spl` (phase 3 of
`doc/05_design/pty_shell_kinds_shs_default.md`) passes its hosted spec
`test/01_unit/os/apps/shell/pty_provider_spec.spl` (2/2, seed
release100-d1ba435a0b3-20261114, macOS arm64). It has NOT run in a SimpleOS guest:

- No QEMU OVMF real-firmware run: not attempted from the macOS host; no SimpleOS
  pane consumer imports the provider yet, so a boot would not exercise it.
- No physical-board run.

Unblock: wire a SimpleOS smux/terminal pane to `os.apps.shell.pty_provider`,
capture an OVMF serial transcript showing `expr 40 + 2` -> `42` and `exit` in a
pane, then repeat on the board (board identity + boot path + transcript).
