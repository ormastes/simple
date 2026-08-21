# Streaming Simplebox Filesystem Applets

Source: `test/01_unit/os/tools/simplebox_fs_applets_spec.spl`

Evidence class: `host-fixture`. These scenarios exercise production streaming
cores with bounded chunks; filesystem image launch is covered separately.

## Scenarios

- `wc` carries words across chunk boundaries without double counting and uses
  byte semantics for invalid UTF-8 and POSIX whitespace.
- `head` returns only the requested newline prefix, preserves remaining line
  state across chunks, and performs no write or read request for zero lines.
- File, byte, and read counts remain explicit and bounded.

