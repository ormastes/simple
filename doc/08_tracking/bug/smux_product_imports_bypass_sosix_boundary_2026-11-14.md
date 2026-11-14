# smux product files import ordinary std owners past the SOSIX host boundary

Status: open. Platform-independent (source scan); observed on macOS arm64,
release/1.0.0 at `3ebbaa03df9`.

## Failing spec

`test/03_system/tools/smux_sosix_boundary_spec.spl` — example "keeps product
leaves and independent Windows clients behind the boundary" (2/3 pass). The
example reads eleven source files and requires every `use std.*` line to be one
of `std.common.*`, `std.sosix.*`, `std.nogc_sync_mut.sosix.*`, `std.io.tcp.{`,
`std.nogc_sync_mut.io.tcp.{`. Three product files fail it (three
`expected false to equal true`). The spec is correct; the imports drifted after
it was written.

## Offending imports

| File:line | Import | Introduced |
|---|---|---|
| `src/os/apps/smux/api.spl:30` | `std.nogc_sync_mut.orchestration.host_helper_settlement_v1.HostHelperSettlementAckV1` | `25d872a717d` (2026-11-07) |
| `src/os/apps/smux/server.spl:17` | `std.nogc_sync_mut.io.file_ops.{file_read, file_write}` | |
| `src/os/apps/smux/server.spl:18` | `std.nogc_sync_mut.io.retained_file.{RetainedPrivateCredentialV1, ...}` | |
| `src/os/apps/smux/server.spl:23` | `std.nogc_sync_mut.io.file_lock_owned_v2.FileLockReleaseStateV2` | |
| `src/os/apps/smux/server.spl:24` | `std.nogc_sync_mut.io.sysinfo_ops.{getpid}` | `5ff1e9885e6` (2026-10-31) |
| `src/os/apps/smux/smux_remote.spl:30` | `std.nogc_async_mut.sosix.environment.{sosix_env_set}` (async facade named directly) | `afba87bf72d` (2026-10-31) |

The other eight scanned files, including the three fixtures, pass.

## Why it was not fixed with the macOS spec port

`src/lib/nogc_sync_mut/sosix/` has no synchronous facade for environment set,
file read/write, retained private credentials, owned file locks or the current
PID, so there is nothing to re-point these imports at. Adding those facades (or
deciding that type-only imports such as `HostHelperSettlementAckV1` and
`FileLockReleaseStateV2` belong on the allowlist) is an owner decision about
the boundary, not a host port.

## Unblock condition

Each import above either goes through a `std.sosix.*` name backed by a
synchronous SOSIX owner, or the owner amends the boundary rule in the spec.
Then the example passes unchanged.

Related: `doc/08_tracking/bug/windows_smux_host_sosix_bypass_2026-10-18.md`.
