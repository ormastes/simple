# Interpreter `rt_file_open` / `rt_file_close` were stubs returning -1 / false

**Date:** 2026-09-05 · **Status:** FIXED in source (uncommitted), deployed seed still affected · **Lane:** `.spipe/sosix_runtime_unification/state.md`

## Defect

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` implemented the
interpreter side of `rt_file_open` as "Simplified - return -1 (not implemented
for interpreter)" and `rt_file_close` as `Ok(Value::Bool(false))`, while the
linked runtime (`runtime/src/value/sffi/file_io/descriptor.rs`) opens a real
descriptor. Every interpreted caller of the typed aliases `file_open` /
`file_close` (`src/lib/nogc_sync_mut/sffi/fs.spl`) therefore got -1 / false on
the seed with no error, so no fd-level I/O could be exercised in interpreter
mode. Found while landing the SOSIX exact POSIX leg (plan task C1).

## Fix

Both wrappers now do the real work (`OpenOptions` + `into_raw_fd`, `libc::close`),
mirroring the runtime's mode table (0 read, 1 read-write, 2 write). Landed with
`rt_fd_pread` / `rt_fd_pwrite` in the same seed change; requires a rebuilt seed.

## Specs

- Reproducing: `test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl` "reads
  bytes at an offset…" asserts `sosix_posix_open` returns a descriptor ≥ 0 and
  `sosix_posix_close` returns true (0/3 on the deployed 2026-09-04 seed, 3/3 on a
  seed built from this change).
- Generalization: same spec, "writes bytes at an offset…" (read-write mode) and
  "reports failures as -errno…" (a closed descriptor yields -EBADF, proving the
  close really closed).
