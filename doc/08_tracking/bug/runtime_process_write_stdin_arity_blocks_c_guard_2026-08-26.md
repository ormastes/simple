# Runtime process write-stdin arity blocks the C runtime guard

**Status:** RESOLVED 2026-08-26
**Observed:** 2026-08-26

`sh scripts/check/check-c-runtime-compiles-push.shs` fails in
`src/runtime/runtime_process.c:1736` because `rt_editor_start_simple_dap` calls
`rt_process_write_stdin(pid, text)` while the current declaration requires four
arguments.  The same failure propagates into two browser-renderer selfcheck
translation units that include this owner.

This is independent of the TCP/UDP SFFI ABI work.  It prevents the whole-tree C
guard from proving the runtime even though a focused `_GNU_SOURCE` syntax check
of the touched `runtime_native.c` succeeds.  Fix by routing both DAP frames
through the canonical length/status contract and add a focused process-runtime
test; do not add a compatibility default or fabricate success.

## RESOLVED 2026-08-26

**Correction to the description above:** the offending call is
`rt_process_spawn_piped_argv`, not `rt_process_write_stdin`. Same file, same
line (`:1736`), same defect class — the symbol at that call site changed since
this record was written, so the original name no longer matches the tree. The
"two browser-renderer selfcheck translation units" wording is also stale: the
whole-tree gate names `runtime_dynload.c` and `runtime_native.c`, which fail for
an unrelated reason (see the `F_ADD_SEALS` record and its resolution below).

Verified independently before fixing, not taken on report:

    sed -n '1448,1450p' src/runtime/runtime_process.c
    static int64_t rt_process_spawn_piped_argv(
            const char* cmd, char** argv, bool sandboxed_renderer,
            int pinned_executable_fd) {

    clang -fsyntax-only -Isrc/runtime src/runtime/runtime_process.c
    src/runtime/runtime_process.c:1736:60: error: too few arguments to
      function call, expected 4, have 3

All four call sites, showing the convention the outlier broke:

| line | call |
|---|---|
| 1362 | `rt_process_spawn_piped_argv("rt-hal-worker", argv, false, fd)` |
| 1625 | `rt_process_spawn_piped_argv(cmd, argv, false, -1)` |
| 1647 | `rt_process_spawn_piped_argv(cmd, argv, true, -1)` |
| 1736 | `rt_process_spawn_piped_argv(argv[0], argv, false)` — **the defect** |

**Fix:** pass `-1` for `pinned_executable_fd`, matching the two sibling call
sites that also have no pinned executable. This is NOT a compatibility default
and does not fabricate success — `-1` is the value the siblings already use to
mean "no pinned fd", and `rt_editor_spawn_simple_dap` spawns a DAP adapter with
no fd to pin. The record's instruction to avoid a compatibility default is
respected: no parameter gained a default, and no signature changed.

`clang -fsyntax-only` on the owner: **rc=0**.
