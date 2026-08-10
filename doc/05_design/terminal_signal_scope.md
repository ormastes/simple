# Scoped terminal signal wakeup design

## ABI

- `rt_terminal_signal_scope_begin() -> i64`: allocate a scope, create a
  nonblocking close-on-exec self-pipe, and install scoped HUP/INT/TERM/WINCH
  handlers while saving prior `sigaction` values. Return `0` on any failure
  after rolling back partial setup.
- `rt_terminal_read_byte_interruptible(scope: i64) -> i64`: `poll` stdin and
  the scope pipe. Return `0..255` for input, `-1` for EOF, `-2` for an orderly
  stop request, `-3` for resize, and `-4` for an I/O or invalid-scope error.
- `rt_terminal_signal_scope_end(scope: i64) -> bool`: restore every saved
  handler, close pipe descriptors, invalidate the handle, and leave raw-mode
  restoration to the owning Simple lifecycle.

## Ownership and safety

Only one terminal signal scope may own the process terminal at a time. Signal
handlers perform no allocation, locking, termios operation, or formatting;
they preserve `errno`, set `sig_atomic_t` bits, and write a byte to the
self-pipe. Pipe saturation is harmless because the pending bit remains
authoritative. Setup blocks the four managed signals until the pipe and all
handlers are ready, restoring the caller's original mask on success or
rollback. A second begin fails without disturbing the active owner.

`run_chat_tui` begins the scope before `enter_raw`; failure is returned as
`signal-scope-unavailable`. Its loop retries after `-3`, exits after `-2`, and
always calls cursor restore, alternate-screen exit, raw-mode exit, then scope
end. Invalid handles, repeated end, or reads after end return the documented
error result with `errno = EINVAL`; they never close a potentially recycled
descriptor. No global atexit callback writes terminal escapes.

The scope is process-global and begin/end are owned by the terminal session
thread. Signal delivery may occur on any thread: a lock-free in-flight counter
guards the short handler section, and teardown retires the descriptor before
waiting for that counter. The runtime panic path restores production raw mode
and the active signal scope directly before abort, without an atexit handler.

## Verification

`test/01_unit/runtime/terminal_signal_scope_focus_test.c` is the red-before
contract. A PTY child enters raw mode and blocks in the scoped read. The parent
sends WINCH then TERM and verifies resize does not exit, TERM wakes promptly,
the child restores termios, and the parent's preinstalled handler is restored
after scope teardown. The existing native focus test redirects stdout through
a real pipe and verifies the TTY boundary reports false.
The same test invokes the production raw-mode APIs, proves panic restoration on
a PTY, and delivers WINCH concurrently with teardown before checking that a
subsequently opened descriptor remains valid.
