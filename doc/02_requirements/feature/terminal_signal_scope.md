# Scoped terminal signal wakeup requirements

Status: selected corrective requirements (2026-08-10)

- REQ-TTY-001: Existing `rt_signal_install` keeps `SA_RESTART`; terminal
  interruption must not alter process-global signal semantics.
- REQ-TTY-002: A terminal session opens an owned signal scope that preserves
  prior handlers and reports installation failure before raw mode is entered.
- REQ-TTY-003: The scope wakes a blocking terminal read through an
  async-signal-safe self-pipe. The handler may only set `sig_atomic_t` state
  and write one byte.
- REQ-TTY-004: Read outcomes distinguish byte, EOF, stop signal, resize
  signal, and I/O failure. SIGWINCH redraws and retries; HUP/INT/TERM exit
  orderly through normal Simple cleanup.
- REQ-TTY-005: Closing the scope restores prior handlers and closes both pipe
  descriptors. Terminal state restoration is scoped to the raw-mode owner;
  no unconditional global atexit escape writes or mutex-taking exit callback
  is allowed.
- REQ-TTY-006: ABI behavior is equivalent in `runtime.c`,
  `runtime_native.c`, `runtime_hosted_signal.c`, the Rust hosted runtime, and
  the tree-walking interpreter registry/provider.
- REQ-TTY-007: Linux PTY tests prove stop wakeup, resize retry, handler
  restoration, and termios restoration. A real stdout-pipe test proves ITF
  color suppression.
