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

## Remaining work

- Remote-PC execution calls a nonexistent three-argument `terminal_execute`;
  the terminal owner needs a real timeout API before the adapter can honor its
  contract. Remote shell commands also need centrally validated repo-relative
  test paths.
- OpenOCD telnet and the std TRACE32 client still build shell command strings.
  Move their protocol execution to bounded TCP/argv owners before accepting
  artifact or command text from metadata.

Do not patch these sites with ad-hoc quoting. The required fixes belong in the
shared environment/process and terminal/protocol owners.
