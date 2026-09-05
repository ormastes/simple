# Terminal signal scope test plan

- REQ-TTY-001/006: source and provider checks preserve legacy `SA_RESTART` and
  verify identical declarations/signatures across core C, native C, hosted C,
  Rust hosted runtime, interpreter registry, and codegen (`bool` / LLVM `I8`).
- REQ-TTY-002/003/004/005/007: canonical Rust runner builds and executes
  `terminal_signal_scope_focus_test.c` against the core runtime archive.
- PTY child uses readiness/ack pipes rather than sleeps, enters raw mode,
  observes resize then stop, restores termios, and proves the prior SIGWINCH
  handler and signal mask return after teardown.
- Negative cases cover second begin rollback, invalid handle, repeated close,
  `EINVAL`, partial-install rollback, an in-flight handler, and exact retired
  write-descriptor reuse with an observable empty pipe.
- Native Simple assertion and Rust-hosted contract entrypoints run under a PTY
  and must restore canonical/echo mode before abort. Windows compile coverage
  is mandatory; live mode/resize coverage reports blocked when no console or
  ConPTY is available.
- ITF integration launches a real Simple subprocess with stdout captured
  directly by the bounded process facade; default and `NO_COLOR` output
  contain no ANSI while force-color does, and the child exit status is retained.
- Run the ITF integration in interpreter and native/provider lanes before
  changing either bug status.
