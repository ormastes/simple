# epoll submit_recv/send/sendfile ignore `epoll_ctl(MOD)` result and test a stale `errno`

- **Date:** 2026-11-24
- **Status:** OPEN
- **Severity:** Medium — a fd can silently miss registration (op never completes), or an unrelated earlier `ENOENT` triggers a spurious `EPOLL_CTL_ADD`
- **Area:** `src/runtime/platform/async_linux_epoll.c:407-410` (`ep_submit_recv`), `:432-435` (`ep_submit_send`), `:457-460` (`ep_submit_sendfile`)
- **Found by:** Fable review of the Linux C dedup plan (work/dedup-linux)

## Summary

```c
epoll_ctl(ed->epoll_fd, EPOLL_CTL_MOD, (int)fd, &ev);
if (errno == ENOENT) {
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, (int)fd, &ev);
}
```

The code ignores the `MOD` return value. `errno` is meaningful only when `MOD` failed. When `MOD` succeeds, `errno` still holds whatever an earlier call left there. That leads to three failure modes:

- An earlier `ENOENT` (from any call) makes a successful `MOD` be followed by an `ADD`. The `ADD` then fails with `EEXIST`, which is harmless but noisy.
- If `MOD` fails with anything other than `ENOENT` (`EBADF`, `EPERM` for regular files, `ENOMEM`), the op is left in the pending map with no interest registered. It never completes, and the submit returns a positive id.
- A failing `ADD` is also ignored, with the same never-completes result.

## Related observed behaviour (pinned, not changed)

`src/runtime/test/async_linux_driver_characterization_selfcheck.c` `t_same_fd_recv_send` covers the case where a recv and a send are pending on one fd. The send's `MOD` replaces the recv's `EPOLLIN` interest, so only the send completes. The recv then stays pending until it is cancelled.

## Fix direction

Write it as `if (epoll_ctl(MOD) != 0) { if (errno != ENOENT || epoll_ctl(ADD) != 0) { int e = errno; map_remove(ed, op); return -e; } }`. Also decide whether interest should be the union of all pending ops on the fd. Pin the new behaviour in the characterization selfcheck first.
