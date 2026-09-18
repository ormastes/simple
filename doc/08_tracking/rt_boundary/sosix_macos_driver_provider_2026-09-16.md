# SOSIX C5 macOS file driver runtime provider classification

Status: classified provider, 2026-09-16.

`src/lib/nogc_async_mut/sosix/macos_driver.spl` owns the hosted SOSIX capsule's
binding of the unified async-driver proactor bridge (`rt_driver_create`,
`rt_driver_submit_read`, `rt_driver_submit_write`, `rt_driver_flush`,
`rt_driver_poll`, `rt_driver_poll_id/result`; declared at
`src/runtime/runtime.h:1582-1600`). These primitives have no lower Pure Simple
host implementation — they ARE the host proactor ABI (kqueue backend in the C
runtime on `__APPLE__`, inline `pread`/`pwrite` executor behind
`backend_name == "rust-syscall"` in the seed). The file may bind and call its
private `rt_driver_*` symbols; consumers may not import them.

Group-ownership criterion (rt_api_group_policy.md Stage 1): 100% of the
`rt_driver_*` group's direct call sites under `src/` live in this one file
(zero existed before 2026-09-16), and the file is the ABI seam itself — the
sosix analog of `src/lib/nogc_async_mut/io/platform_event.spl`, which binds the
kqueue readiness externs the same way.

Scope notes (measured 2026-09-16 on macOS arm64, seed rebuilt 2026-09-14):

- File reads/writes complete off the kqueue event loop on every current
  backend (C runtime: pthread pool, `src/runtime/platform/async_macos.c`;
  seed: inline at flush). The provider claims the proactor pipeline and real
  `-errno` read/write completions, not kqueue-evented file I/O.
- `rt_driver_submit_open` is deliberately NOT bound: the bindings declare a
  4-parameter extern for a 5-parameter ABI and drop `path_len`, leaving `mode`
  in an uncontrolled register — the same `O_RDONLY` open returned `-22`
  (EINVAL) in one process and a valid fd in another
  (probe sources inlined in the Appendix of
  `doc/08_tracking/bug/rt_driver_poll_data_interpreter_marshalling_2026-09-16.md`;
  scratchpad copies deleted 2026-09-17). Descriptor
  opens stay on the deployed C1 pair `rt_io_file_open`
  (`std.nogc_sync_mut.sffi.fs`); that extern collapses open errors to `-1`,
  so missing-file rows assert a negative native code rather than a specific
  errno.
- `rt_driver_poll_data` is deliberately NOT bound: the runtime returns a
  NaN-boxed string word, correct under the JIT but read as a raw pointer by
  the interpreter (right-length header garbage), and spec files always run
  interpreted on this seed (std.spec's closure-returning `skip` decorator
  makes the JIT bail silently). Read bytes are materialized with a positioned
  re-read through the deployed typed alias `file_read_text_at` after the
  proactor completion reports success. Full writeup:
  doc/08_tracking/bug/rt_driver_poll_data_interpreter_marshalling_2026-09-16.md.

Public surface: `SosixMacosFileDriver` (a `SosixSyncWaitDriver` over the ring,
constructed with `create()`, torn down with `shutdown()`), re-exported from
`std.nogc_async_mut.sosix`. Evidence:
`test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl` (macOS-only rows).
