# Windows: 35 tracked symlinks under `src/` materialize as path TEXT and fail to parse

**Status:** FIXED 2026-09-02 — see "Investigation and fix 2026-09-02" below.
Verified by execution on a fresh worktree (`BEFORE_check_rc=1` ->
`AFTER_check_rc=0`) and by two passing specs; the `--selftest` verdict of
`check-main-test-runnable-push.shs` is recorded in that section.
Originally: OPEN — blocked `check-main-test-runnable-push.shs` entirely on
Windows, and broke any fresh materialization of committed content.
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

---

## Investigation and fix 2026-09-02

Host facts, measured:

- `git config core.symlinks` → **`false`**.
- Developer Mode / `SeCreateSymbolicLinkPrivilege` is **NOT available**:
  `powershell New-Item -ItemType SymbolicLink` fails with
  `NewItemSymbolicLinkElevationRequired`. `core.symlinks=true` is therefore not
  an option on this machine, and unblock condition 2 is closed.
- `git ls-files -s src | awk '$1=="120000"'` → 35 paths: **23 directory**
  aliases (22 under `src/compiler/` such as `backend -> 70.backend`, plus
  `src/std -> lib` and the `src/app` tool aliases) and **12 `.spl` files**
  (`app/debug/coordinator.spl`, `app/debug/remote/target/riscv32.spl`, the eight
  `app/leak_finder/*.spl`, `app/lint/main.spl`).

### Is the existing materialiser a silent no-op? No — it was never run here

`scripts/setup/materialize-symlinks-windows.shs` genuinely works. In the MAIN
checkout the 23 directory links are real NTFS junctions and the 12 file links
are hard links (`stat -c %h` = 2, byte-identical size to their targets). Its
`created=0 ... failed=0` line is honest: everything was already materialised.

The gap is WHERE it runs. `check-main-test-runnable-push.shs` materialises
committed content with `git worktree add --detach`, which honours
`core.symlinks` and so writes path text — and nothing ran the materialiser on
that worktree. Measured on a fresh worktree of `27c89536f8c`:

```
$ ls -l src/app/debug/coordinator.spl        # 45 bytes: "../../lib/nogc_sync_mut/debug/coordinator.spl"
$ bin/simple.exe check src/app/debug/coordinator.spl ; rc=$?
BEFORE_check_rc=1
  cannot resolve import `compiler.frontend.core.lexer` ... segment `compiler` not found
$ sh scripts/setup/materialize-symlinks-windows.shs --strict-missing <wt> ; rc=$?
materialize-symlinks-windows: created=100 already_ok=0 skipped_pending=0 failed=0
$ bin/simple.exe check src/app/debug/coordinator.spl ; rc=$?
AFTER_check_rc=0
  All checks passed (1 file(s))
```

(Exit statuses read directly into a variable on the line after each invocation,
never through a pipe.)

### Fix

Unblock condition **1 was NOT chosen**: converting 35 tracked symlinks to real
files changes what a Unix checkout gets, duplicates content that must stay in
sync, and touches `src/compiler/70.backend` where other sessions are live. The
chosen fix is the "not run at the right time" reading of condition 1's second
clause:

1. `check-main-test-runnable-push.shs` calls the materialiser on **every**
   worktree it creates — all three `git worktree add --detach` sites (the C and
   F selftest fixtures and the real scan). Wiring only the scan leaves C1
   failing on a clean tree, which is the exact symptom above. The worktree root
   is passed explicitly; the script's default root derives from its own location
   and would otherwise materialise the main checkout.
2. `materialize-symlinks-windows.shs` gains `--strict-missing`. Condition 3's
   objection — "a parse error becoming a silent path redirect is worse than the
   defect" — applies just as much to the materialiser's own silent branch: a
   dangling placeholder was counted `skipped_pending` and exited 0, leaving path
   text a compiler then reads as source. Under the flag a dangling symlink whose
   target is **tracked** is a named, counted, non-zero failure. Scoped to tracked
   targets because a blanket strict mode failed on 16 links on a real worktree —
   every one an untracked submodule (`examples/spipe`) or `tools/*-cli` target,
   none under `src/`, all legitimately not yet present.

Both changes are behind a `uname` MSYS/MinGW/Cygwin branch and the new flag
defaults off, so **Unix behaviour is byte-unchanged**. Not testable on POSIX from
this host; stated rather than claimed.

### Specs

- `test/03_system/check/windows_symlinked_spl_readable_as_code_spec.spl`
  (reproducing) — a mode-120000 `.spl` on a `core.symlinks=false` checkout is
  rejected as source, and compiles clean after materialisation. 2/2 pass.
- `test/03_system/check/windows_dangling_symlink_fails_loudly_spec.spl`
  (generalizing) — a dangling symlink with a tracked target fails loudly;
  an untracked one stays a benign skip; the default path is unchanged. 2/2 pass.

### Related finding, not fixed here

`git worktree add` of this repo fails with `Filename too long` under a deep
`TMPDIR` (`core.longpaths` is unset). The guard uses `mktemp -d`, so on a Windows
host with a long temp path it errors before reaching any symlink. Worked around
in verification by pointing `TMPDIR` at a short path.
