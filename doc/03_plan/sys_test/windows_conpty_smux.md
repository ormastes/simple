<!-- codex-design -->
# Windows ConPTY for SMUX Test Plan

- REQ-001/004: exercise open, spawn, write, read, and close through interpreter and native paths.
- REQ-002: run a command through ConPTY on Windows and verify captured output.
- REQ-003: guard that SMUX reaches `std.sys.pty` through synchronous SOSIX and has no `rt_pty_*` declarations.
- REQ-005/NFR-002: invalid handles fail safely and repeated close does not crash.
- NFR-001: empty read returns within the requested timeout.
- NFR-003: retain existing Unix PTY unit coverage.
- REQ-006: `test/03_system/tools/smux_sosix_boundary_spec.spl` rejects raw host
  bypasses and async layering; negative controls prevent a vacuous source pass.
  Its manual is `doc/06_spec/03_system/tools/smux_sosix_boundary_spec.md`.
- REQ-006: native `smux_sosix_host` entrypoint checks normalized argv, an existing
  file, PID, clock/sleep, Unicode tagged stdin and EOF. Run under a ten-second
  external process-tree watchdog with exact stdout/exit evidence. Source-only
  guards do not qualify its runtime behavior.
- Rebuild both independent Windows product fixtures and smux with the selected
  Windows overlay; preserve their actual client/child output and terminal cleanup
  evidence. Do not replace these runs with architectural source checks.
