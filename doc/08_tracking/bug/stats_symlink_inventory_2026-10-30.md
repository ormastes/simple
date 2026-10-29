# Stats inventory imported an unroutable mock symlink predicate

Status: candidate repair; native filesystem regression pending.

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
and SLOC, and refusal to scan a symlink root. Build/runtime receipts will be
added after execution; source review alone does not establish native PASS.
