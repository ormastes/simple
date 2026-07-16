# Test daemon remaining transport safety

Status: Open.

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

## Remaining work

- Remote-PC remains unreachable from production registration because no
  terminal configuration source is defined for the daemon.
- Remote test paths are safely shell-quoted but are not yet restricted to a
  centrally validated repo-relative policy.

The remaining fixes belong in the shared configuration and path-policy owners.
