# Cross-platform `sys_get_args` requirements

The user selected all supported targets: macOS, Linux, Windows, BSD, and
SimpleOS.

- REQ-001: `sys_get_args()` returns `argv[0]` followed by every user argument in
  original order for interpreter, JIT, SMF, and native execution.
- REQ-002: all aliases read the same store populated by startup.
- REQ-003: Windows preserves Unicode arguments through a wide-character entry.
- REQ-004: a missing startup provider fails linking; no empty/no-op fallback may
  fabricate success.
- REQ-005: SimpleOS strong SimpleCore providers override coherent weak libc
  fallbacks without disconnected symbol names.
