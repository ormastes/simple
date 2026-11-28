# C epoll token table is process-wide and lossy for large fds (2026-11-28)

Status: open (found in review of PR #12418)

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
