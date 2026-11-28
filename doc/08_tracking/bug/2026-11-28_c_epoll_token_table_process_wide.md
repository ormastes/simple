# C epoll token table is process-wide and lossy for large fds (2026-11-28)

Status: verification-pending (epoll loop handle is now a per-loop RtEvLoop with a growable fd->token table, no fd cap, cleared on deregister; no shared statics, no lock. Fallback rule for all three lanes: an fd with no registered token reports the fd (C, Rust net.rs, interpreter now agree). Doc comment states ERR/HUP-only => Read. Prevention: src/runtime/test/rt_event_loop_token_selfcheck.c (real epoll/kqueue). Verified on Windows only with a fake-syscall harness + clang -fsyntax-only; needs a Linux run)

`src/runtime/runtime_native.c` keeps `poll_tokens_by_fd[65536]` for the epoll backend:
- one table per process, not per loop: the same fd registered in two loops with
  different tokens keeps only the last token for both;
- `rt_event_loop_deregister` does not clear the slot (harmless for polling, stale data);
- for fd >= 65536 the token is silently the fd number, not the registered token;
- an unregistered fd reads token 0 in C but the fd in the Rust runtime (`net.rs`
  `unwrap_or(handle)`), an unspecified cross-lane difference. Pick one.

Fix: store the token in the epoll event itself (a small per-loop registration table
keyed by (epfd, fd), or `epoll_event.data.ptr` to a registration record) and clear it on
deregister. Also state in the doc comments that error/hangup-only events report Read.
Also lockless-by-default applies: the existing statics are unsynchronised; per-loop state
removes the need for a lock.
