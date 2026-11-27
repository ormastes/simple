# Stats inventory imported an unroutable mock symlink predicate

Status: native filesystem regression passed; full CLI qualification remains separate.

Attempt 7's CLI HIR build failed in `app/stats/inventory_scan_v2.spl:63:12`
with `unresolved name: file_is_symlink`. This was its one FAILED module;
1,013 other inventory entries were BLOCKED/incomplete. Evidence is the
`compiler_cli_build.log` in the attempt-7 compiler verification directory.

The imported `std.nogc_sync_mut.file_system` facade lists a bare export without
an import/provider route. Its `metadata.spl` implementation is explicitly a
mock returning false. Routing the import directly to that implementation would
compile away the diagnostic while leaving directory-link recursion possible.

The stats adapter now uses existing host operations through `app.io.mod`:
`dir_is_real_no_follow` admits recursive directory traversal, and
`file_is_regular_no_follow` admits file content reads. The scan root receives
the same directory check. Their existing native providers use POSIX `lstat`
with `S_ISDIR`/`S_ISREG`; Windows providers reject reparse points. No runtime ABI
or provider implementation changes are needed. Special files are excluded as
well as file, directory and dangling symlinks. This ordinary repository scan
does not claim race-resistant traversal against concurrent path replacement.

The general legacy `file_system.metadata.file_is_symlink` mock and its facade
remain unresolved library defects; this repair removes the stats dependency
on them rather than treating them as working APIs.

`test/01_unit/app/stats/inventory_symlink_probe.spl` requires a real temporary
fixture: two real source files, a file symlink, directory symlink, dangling
symlink and directory cycle. It checks both predicates, exact returned paths
and SLOC, and refusal to scan a symlink root.

Native execution passed once with exit 0 using admitted pure-Simple producer
`a9ed5e4b92a811fa14f5ae351948c8d4350527f966139ea72ac13ccee3633e4f`.
The first single-thread build timed out after 28/103 HIR modules; its cache was
preserved for a 20-thread bounded continuation, which completed with peak
5,076,788 KiB and unchanged source snapshot
`6b1cd7e22692dcab2d58f74c87361e0c623f2f6c68489466ca99f08d527b5b62`.
Receipts are in `/tmp/simple-stats-symlink-admitted7-continuation-20261030`:
`filesystem-fixture.sdn` records verified symlink objects and exact readlink
targets; `runtime-result.sdn` and `run.log` record the real executable result.
Artifact SHA256:
`837b1ab3d5cd96a72f8c7ff51fddbc13d607a151c0507d44b070aaa1eb140f40`.
This proves the focused filesystem contract, not a full CLI or release PASS.
