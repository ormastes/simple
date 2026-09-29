<!-- codex-design -->
# Windows ConPTY for SMUX Test Plan

- REQ-001/004: exercise open, spawn, write, read, and close through interpreter and native paths.
- REQ-002: run a command through ConPTY on Windows and verify captured output.
- REQ-003: guard that SMUX imports `std.sys.pty` and has no `rt_pty_*` declarations.
- REQ-005/NFR-002: invalid handles fail safely and repeated close does not crash.
- NFR-001: empty read returns within the requested timeout.
- NFR-003: retain existing Unix PTY unit coverage.
