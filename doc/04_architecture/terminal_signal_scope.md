# Scoped terminal signal architecture

The terminal session owns a single opaque runtime scope. Each runtime provider
implements the same three-function ABI and keeps the legacy signal latch ABI
unchanged. The scope owns saved handlers, a nonblocking self-pipe, pending
signal bits, and teardown state. Simple owns raw mode, screen state, and the
cleanup order.

The signal handler is restricted to `sig_atomic_t` writes and a best-effort
single-byte pipe write preserving `errno`. Setup blocks HUP/INT/TERM/WINCH
while creating the pipe and installing handlers, then restores the caller's
mask. Partial failure restores every installed handler and closes every opened
descriptor. Teardown is idempotence-safe: first close succeeds; repeat close
fails with `EINVAL` without touching recycled descriptors.

`rt_terminal_read_byte_interruptible` polls stdin and the self-pipe. It drains
the pipe, snapshots and clears pending bits, prioritizes stop over resize, and
returns distinct ABI codes. EOF is never treated as a signal. SIGWINCH causes
the Caret loop to resize/redraw and retry; HUP/INT/TERM returns through the
normal cursor/screen/raw restoration path before scope teardown.
