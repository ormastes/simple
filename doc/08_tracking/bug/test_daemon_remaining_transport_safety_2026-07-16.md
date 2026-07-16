# Test daemon remaining transport safety

Status: Closed for the reviewed transport scope.

Date: 2026-07-16

## Fixed in the current hardening lane

- The broker now retains and dispatches concrete adapters instead of discarding
  them as inert `SessionAdapter.base` values.
- Session-key IDs hash every matching field, including reset policy, and each
  started lease receives a unique instance suffix.
- Container lifecycle and test execution use structured argv with host-owned
  deadlines; no container command uses `rt_shell_exec`.
- GUI, service, OpenOCD, and TRACE32 child tests share the same captured-output
  deadline owner. Their temporary environment is restored after synchronous
  execution. Core C lacks `rt_env_remove`, so previously absent keys restore to
  the portable empty value; exact absence and concurrent dispatch require a
  runtime env-aware run API.
- Remote-PC execution now uses the shared bounded SSH/Telnet dispatcher and
  POSIX-quotes the test path. Telnet reads share one absolute deadline.
- OpenOCD uses the shared bounded telnet client, validates program paths, and
  starts with structured argv. All three TRACE32 profile owners use bounded
  structured argv for discovery and commands.
- T32 SWD forwards caller deadlines into the TRACE32 process owner. Relay
  scripts use bounded structured argv for execute, send, and receive.
- Remote execution accepts only repo-relative `test/*.spl` paths without
  traversal, alternate separators, or control characters.

## Remaining work

- None in the reviewed transport scope. Production daemon startup parses the
  canonical `config/t32/t32_terminal.sdn`, registers SSH/Telnet terminals by
  name, and dispatches remote-PC metadata targets to the matching adapter.
