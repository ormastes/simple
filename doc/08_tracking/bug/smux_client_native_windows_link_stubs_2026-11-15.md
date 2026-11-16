# smux_client.exe (native, Windows) linked 57 aborting stubs (2026-11-15)

Status: verification-pending (import-narrowing slice); remaining groups open

## Symptom
Phase-1 seed `native-build src/app/hosted_apps/smux_client.spl` on Windows:
`stubbed 52 unresolved symbol(s)` plus `Generating 5 stub functions`. Each stub
prints its name and aborts when called.

## Classification (measured with llvm-nm over the build cache)
| group | count before | count after | class | owner object |
|---|---|---|---|---|
| `rt_db_*` (18), `rt_browser_http_job_*`, `rt_profiler_*`, `rt_tls13_*`, `rt_select/rank_query`, macro/debug/time/concurrent (28 total) | 28 | 0 | (a) over-broad import | `sffi/host.spl`, pulled in only by `file_system/permissions.spl` for `package_chmod` |
| `sosix_file_read` (compile stub) | 1 | 0 | (a)/wrong owner, reachable from `--serve-owner-file` | `sosix/host.spl` re-exported it from `io.file_ops`, which only imports it privately |
| `rt_local_unix_*_v1` | 18 | 18 | (b) reachable (runtime binding/control sockets) | `io/local_ipc_v1.spl`; C backing is `!_WIN32` only in `runtime_socket_nonblock.c` |
| `rt_retained_private_credential_*_v1` | 6 | 6 | (b) reachable (`server.spl` owner-file credential) | `io/retained_file_abi.spl`; C backing is `__linux__` only |
| `<importer>__SOSIX_PTY_SHELL_{NATIVE,SHS}` (compile stubs) | 4 | 4 | compiler defect, unreferenced | `interactive_protocol.spl`, `smux_remote.spl` import only `sosix_pty_default_shell`, yet the aliased const re-exports of `sosix/pty.spl` are emitted as importer-scoped symbols |

Totals: 57 -> 28 (link 52 -> 24, compile 5 -> 4). `smux_client.exe --help` rc=0
before and after. No `rt_db_*` symbol is reachable, so no embedded-DB backing
is needed for smux_client.

## Fix (this slice)
- `io/file_ops.spl`: `package_chmod` wrapper over its existing `rt_package_chmod` extern.
- `file_system/permissions.spl` (sync + async): import it from `io.file_ops`, not `sffi.host`.
- `sosix/host.spl`: `sosix_file_read` re-exported from its owner `io_runtime`.
- Spec: `test/01_unit/lib/sosix/host_file_chmod_owner_spec.spl` (2/2).

## Plan for the open groups (not half-implemented here)
1. `rt_local_unix_*_v1` on Windows: same multi-day AF_UNIX port already deferred
   in `native_windows_rt_pty_link_stubs_conpty_c_lane_2026-11-15.md`
   (afunix.h, Win10 1803+, peer identity via `SIO_AF_UNIX_GETPEERPID`, handoff
   semantics). smux_client's runtime-binding / runtime-control paths need it.
2. `rt_retained_private_credential_*_v1` on Windows: needs a Windows backing
   (owner-only DACL file + `MoveFileExW` no-replace publish, `BCryptGenRandom`)
   matching the Linux contract in `runtime_retained_private_credential_v1.c`.
   Owner/semantics review first; until then `--serve-owner-file` aborts on
   Windows when it reaches the credential.
3. Compiler: aliased `export use X.{CONST as ALIAS}` in a facade must not emit
   importer-scoped const symbols for names the importer never imported.

## Update 2026-11-16: the 24 stubs were an archive-membership gap, not a missing C backing

Correction to the table above. `runtime_socket_nonblock.c` defines all 18
`rt_local_unix_*_v1` leaves outside any `#if`; on hosts other than Linux and
Darwin each one returns unsupported (-4). `runtime_retained_private_credential_v1.c`
has a non-Linux `#else` that defines all 6 credential leaves, each returning -1.
Both TUs compile for `x86_64-w64-windows-gnu` (llvm-mingw clang). The only
undefined references are `rt_array_new/push/set/free` and `rt_value_int`, which
`runtime_native.c` already owns.

Neither TU was a member of the seed's core-C runtime archive
(`native_project/tools.rs` `build_c_runtime_library`), so the Windows link
stubbed all 24 as abort-on-call stubs. Fix (this slice): both TUs and their
headers were added to that list. The credential caller
(`retained_file.spl:645`) maps `token <= 0` to `state: "unavailable"`, so it
fails closed rather than aborting.

Baseline (phase-1 seed `seed-vtable.exe`, release tip `a0d424f8a2a`):
`[native-link] stubbed 24 unresolved symbol(s)` plus `Generating 4 stub functions`.
After: not measured. The list is compiled into the seed binary, and this lane
was not authorized to rebuild the seed. The next seed rebuild should show
`stubbed 0`, with only the 4 `SOSIX_PTY_SHELL_*` compile stubs left.

### Still open (named gaps, not filled)
- **Real Windows AF_UNIX backing for `rt_local_unix_*`.** Windows 10 1803+
  supports `AF_UNIX` `SOCK_STREAM` via `afunix.h`. The v1 owner contract has no
  faithful mapping yet:
  - `expected_uid` and the no-follow, non-writable-ancestor parent walk are
    POSIX uid/mode concepts. Windows needs an owner-SID/DACL equivalent.
  - Peer identity would come from `SIO_AF_UNIX_GETPEERPID`, which is PID only
    with no uid/gid.
  - `SOCKET` is not an `int fd`.
  - A listener node must be removed with `DeleteFileW`.
  - There is no `SCM_RIGHTS`, so `stage_stdout`, `adopt_byte_endpoint`,
    `read_handoff_now` and `handoff_state` must stay -4 permanently.

  This needs an owner/semantics design review first, the same as the POSIX
  design doc. Until then smux runtime-binding and runtime-control on Windows get
  -4 (unsupported) instead of an abort.
- **Windows credential backing.** Unchanged from plan item 2. It needs owner
  review against `doc/05_design/smux_retained_private_credential_v1.md`.
