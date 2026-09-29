<!-- codex-design -->
# Windows ConPTY for SMUX

The user selected native Windows ConPTY support exposed through a pure-Simple
PTY API and consumed by SMUX.

- REQ-001: `std.sys.pty` provides open, spawn, read, write, close, and default-shell operations.
- REQ-002: Windows uses ConPTY; Unix retains the existing PTY implementation.
- REQ-003: SMUX imports the Simple PTY API and contains no raw PTY extern declarations.
- REQ-004: interpreter and native execution expose equivalent PTY behavior.
- REQ-005: resource failure returns a typed/false result and releases owned handles.
