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
