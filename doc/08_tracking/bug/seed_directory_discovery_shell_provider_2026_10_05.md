# Windows seed directory discovery selects a shell-dependent facade

The pinned Phase1 seed `283f863a490d0d6a1359deaefc6506a0023c3357ef079537830fcca63333572f`
started the canonical whole runner after the hash export repair, but discovered
zero specs and zero SPL doctests. Markdown ran 20 blocks (19 passed, one failed);
the whole callback correctly rejected the incomplete summary as infrastructure
failure. Zero discovery was never accepted as whole-suite success.

An owned 20-slot diagnostic on 2026-10-05 found two real nested sentinel files
through `rt_dir_walk`, but zero through either public facade and through the
test-runner import closure. A separate bounded call trace proved that importing
`std.io_runtime.dir_walk` dispatched to `dir_ops.dir_walk`, then `_dir_shell`
and `process_run`. That implementation required `/bin/sh` and turned provider
failure into an empty inventory on Windows. The underlying shared-name import
resolution remains a separate compiler concern.

The source workaround makes the selected facade use the existing native walk,
normalizes only Windows host paths, and retains sorted output. It does not
change test configuration, platform selectors, pending cases, or assertions.
The legacy ABI still cannot distinguish an absent/unreadable directory from
an empty one; callers requiring authoritative inventory must retain their
existing coverage gates.

`test/04_smoke/phase1_directory_discovery.spl` requires exactly three real files,
including nested, quoted, spaced, and Unicode names, through both facades and
checks an absent directory separately. Source repair qualification is pending;
no native, MCP, or whole-suite PASS is claimed by this checkpoint.
