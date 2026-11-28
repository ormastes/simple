# io_uring submit: `bufs_put` ENOMEM arms after SQE prep are unreachable dead defensive code

- **Date:** 2026-11-24
- **Status:** FIXED (2026-11-28)
- **Severity:** Low — dead code; it would be wrong if it ever became reachable
- **Area:** `src/runtime/platform/async_linux_uring.c` — the `if (!bufs_put(...)) { free(..); return -ENOMEM; }` arms in connect, recv, send, read, write, open and timeout (release/1.0.0 lines 373, 403, 434, 498, 530, 559, 624)

## Summary

Each submit function calls `bufs_ensure(ud)` first and returns `-ENOMEM` if that fails. `bufs_put` calls `bufs_ensure` again with the same `bufs_count`. The first call guaranteed `count*10 < cap*6`, so the second call cannot grow the table and cannot fail. The `bufs_put` failure arm is therefore unreachable.

This is **not a live use-after-free.** It would only become one if the arm were reachable. The arm runs after `io_uring_prep_*` has already queued an SQE that points at the buffer, so it would free memory the kernel will still read or write once the next `flush` submits that SQE.

## Fix direction

Make the invariant explicit. Have `bufs_put` insert without re-checking (callers already ran `bufs_ensure`), or move the insert before `get_sqe` and roll it back on `-EAGAIN`. Either way, the failure arm can then be deleted. Behaviour is pinned by `src/runtime/test/async_linux_driver_characterization_selfcheck.c` (`t_uring_ring_full`, `t_uring_einval`).

## Resolution (2026-11-28)

`bufs_put` in `src/runtime/platform/async_linux_uring.c` now returns `void`, asserts the `bufs_ensure(ud)` precondition (`bufs_cap > 0 && bufs_count * 10 < bufs_cap * 6`), and delegates directly to `bufs_insert_no_grow` without calling `bufs_ensure`. The unreachable post-`io_uring_prep_*` `-ENOMEM` / `free(...)` arms in `uring_submit_connect`, `uring_submit_buffered` (covering recv/send/read/write), `uring_submit_open`, and `uring_submit_timeout` are removed. `src/runtime/test/async_linux_driver_characterization_selfcheck.c` extends `t_uring_ring_full` to `submit_open`/`submit_connect` `-EAGAIN` paths and adds `t_uring_bufs_grow_and_drain` (80 in-flight ops resizing the buffer table `64 -> 128 -> 256` and draining on `destroy`).
