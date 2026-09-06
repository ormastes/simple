# `io_spec` red: `semantic: variable vfs_ipc_request_bytes not found`

Filed 2026-09-05. Status: CLOSED 2026-09-05 (pre-existing; reproduced BEFORE and AFTER the
`os.sosix.core` lift). The failing examples were source-text assertions over
`src/os/sosix/io.spl` and `io_rw.spl` (the grep-a-spec anti-pattern, spipe skill);
`io.spl` was deleted as dead and the three examples were replaced in the same change
by behavior examples on the `io_rw` route (`test/01_unit/os/sosix/io_spec.spl`,
describe "SOSIX legacy fd route behavior"): EBADF for an invalid fd, zero-length
serial completion, and EAGAIN (-11) on slot exhaustion. `Results: 9 total, 9 passed`.

## Symptom

`bin/simple test test/01_unit/os/sosix/io_spec.spl --no-session-daemon`
-> `Results: 9 total, 8 passed, 1 failed`; failing example
`uses the shared named VFS request owner rather than a fixed VFS port`
(describe "SOSIX VFS copied request convergence"), `semantic: variable
vfs_ipc_request_bytes not found`.

## Where to look

`src/os/sosix/io_rw.spl:4` imports `os.userlib.fs.{vfs_ipc_request_bytes}`; the
seed interpreter resolves the module but not the symbol on this path. Check
whether `os.userlib.fs` exports it (`E0410`: `pub` alone exports nothing) and
whether the spec reaches it through `os.sosix.io_state` re-exports. Plan task
G2 rewrites this route onto the v1 positioned stack, which removes the import;
the example must be re-read at that point rather than deleted.
