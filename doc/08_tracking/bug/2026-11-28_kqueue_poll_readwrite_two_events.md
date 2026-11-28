# kqueue rt_event_loop_poll reports ReadWrite as two events (2026-11-28)

Status: open (found in review of PR #12418)

`src/runtime/runtime_native.c`, kqueue `rt_event_loop_poll`: a registration with
`mode == 2` installs separate EVFILT_READ and EVFILT_WRITE filters, so one fd that is
both readable and writable yields two entries (ready 0 and ready 1). The epoll C path,
the Rust runtime and the interpreter coalesce them into one entry with ready == 2.
The interpreter's kqueue backend already coalesces by (fd, token).

Fix: merge entries with the same (fd, token) into ready == 2 before filling
`poll_results/poll_ready/poll_tokens`.
Repro/prevention: needs a macOS/FreeBSD lane (`scripts/check/check-freebsd-bootstrap-qemu.shs`)
spec registering a read+write fd with mode 2 and expecting exactly one triple with ready 2.
