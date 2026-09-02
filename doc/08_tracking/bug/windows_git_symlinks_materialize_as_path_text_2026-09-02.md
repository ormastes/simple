# Windows: 35 tracked symlinks under `src/` materialize as path TEXT and fail to parse

**Status:** OPEN 2026-09-02 — blocks `check-main-test-runnable-push.shs` entirely
on Windows, and breaks any fresh materialization of committed content.
**Severity:** Blocking — a push-tier gate cannot run at all; a fresh Windows
clone cannot compile its own startup path.
**Affected:** 35 paths, `git ls-files -s src | awk '$1=="120000"'`
**Path:** `bug` track.

## Symptom

```
$ sh scripts/check/check-main-test-runnable-push.shs --rev HEAD
SELFTEST FAIL: C1 — the clean worktree already fails with a parse diagnostic
  (fail:rc=1: error: compile failed: parse: in
   "\?\C:\Users\ormas\AppData\Local\Temp\tmp.P7G9zV5zAq\c\src\app\debug\coordinator.spl":
   Unexpected token: expected expression, found Slash), so injecting one proves nothing
check-main-test-runnable-push.shs: FAIL — selftest failed; no scan was run
```

Reproduced twice, on `88ea1ede016` and after, with `bin/simple.exe`
md5 `d52d770724a9f8797e98ac7819709ab9`.

## Root cause

`src/app/debug/coordinator.spl` is a git **symlink** (mode `120000`). Its blob
content is one line:

```
../../lib/nogc_sync_mut/debug/coordinator.spl
```

This repo is checked out with `core.symlinks=false` (measured), so git writes
that blob as a **regular file containing the target path as text**. The compiler
then parses `../../lib/...` as Simple source: `..` is consumed, the next token is
`/`, and the parser reports exactly **`expected expression, found Slash`**.

`git ls-files -s src | awk '$1=="120000"' | wc -l` → **35** such paths, including
`src/app/debug/coordinator.spl`, `src/app/cmm_lsp`,
`src/app/debug/remote/target/riscv32.spl`, and the whole
`src/app/leak_finder/**` set — all on the compiler's startup path.

The working tree escapes this only because those files were manually
materialized with real content, which makes them show as **dirty**:

```
$ git diff HEAD --stat -- src/app/debug/coordinator.spl
 src/app/debug/coordinator.spl | 16 +++++++++++++++-   (mode 120000)
```

So the working tree parses (`bin/simple.exe check` → clean) while the COMMITTED
content does not. The guard is right and the tree is wrong: it materializes
committed content into a temp worktree, which is exactly what a fresh clone or
a CI checkout gets.

## Why no other guard caught it

Every other push-tier guard checks trees, ranges, symbol sets, or C that parses
under `-fsyntax-only`. None loads a `.spl` with the Simple compiler.
`check-main-test-runnable-push.shs` exists precisely for that, and it is the one
guard that cannot run here.

## Unblock condition

Any ONE of:

1. Replace the 35 tracked symlinks with real files (or with an in-language
   re-export shim, which is what `src/app/debug/coordinator.spl`'s dirty
   working-tree copy already is). This is the portable fix and removes the
   dependency on `core.symlinks` entirely.
2. Enable Windows symlink creation repo-wide (Developer Mode +
   `git config core.symlinks true` + re-checkout). Fragile: it needs a per-machine
   privilege and silently degrades back to text files when absent.
3. Teach the compiler's module loader to detect a one-line body that resolves to
   an existing `.spl` path and follow it. Rejected as written — it makes a parse
   error into a silent path redirect, which is worse than the defect.

Option 1 is the recommendation.

## Cross-platform note

Nothing was changed to produce this record. On Linux and macOS the symlinks
resolve normally and the guard passes; the defect is Windows-only, and any fix
must not alter Unix resolution behaviour.
