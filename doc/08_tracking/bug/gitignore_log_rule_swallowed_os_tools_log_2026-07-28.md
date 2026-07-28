# `.gitignore` blanket `log/` rule silently un-tracked `src/os/tools/log/` (2 source files lost from git)

**Status:** FIXED 2026-07-28
**Found:** 2026-07-28 (dangling-reference triage, `src/os/**` + `src/unit/**` scope)
**Area:** `.gitignore`, `src/os/tools/log/`
**Severity:** high — **lost work**. Two complete, working SimpleOS source files
existed on disk but were invisible to git, so they were absent from every clone,
every release tarball, and every CI checkout.

## Finding

`.gitignore:62` carries a blanket build-artifact rule:

```
# Logs
log/
```

Git pathspec `log/` matches **any** directory named `log` at any depth, so it
swallowed the SimpleOS log-tools source directory `src/os/tools/log/`, taking
both files with it:

| File | Size | Contents |
|------|------|----------|
| `src/os/tools/log/journal.spl` | 3808 B | `struct JournalFilter`, `class JournalReader`, `fn facility_name`, `fn level_name`, `fn level_color`, `fn _format_timestamp` |
| `src/os/tools/log/log_viewer.spl` | 3392 B | `fn run_log` — the SimpleOS `log` CLI command (follow mode, `--level=`, `--source=`, `-n`) |

Neither was tracked:

```
$ git check-ignore -v src/os/tools/log/journal.spl
.gitignore:62:log/	src/os/tools/log/journal.spl

$ git ls-files -- src/os/tools/log/
(empty)
```

`git status` did **not** surface them either — ignored files are suppressed —
so the loss was completely silent.

## This is a known, recurring hazard in this repo

The same rule had already eaten five other source directories, each patched
reactively with a one-off negation:

```
log/
!src/compiler_rust/vendor/log/
!src/os/kernel/log/
!src/lib/log/
!src/lib/nogc_async_mut_noalloc/log/
!test/os/kernel/log/
```

`src/os/tools/log/` is the sixth and was simply missed. The pattern of five
prior exceptions is the evidence that the blanket rule is mis-scoped, not that
each directory is a special case.

## Live breakage this caused

`src/os/tools_test.spl` is tracked and imports the ignored file:

```
src/os/tools_test.spl:28:  use os.tools.log.log_viewer.{run_log}
src/os/tools_test.spl:166:     val r1 = run_log([])
src/os/tools_test.spl:170:     val r2 = run_log(["-n", "5"])
```

A fresh clone therefore cannot resolve `os.tools.log.log_viewer` at all — the
importing test is unbuildable for anyone who did not happen to have the
untracked files sitting in their working copy.

It also produced 4 findings in `scripts/check/check-dangling-references.shs`
(1 MODULE + 3 SYMBOL), because the checker indexes definitions from
`git ls-files` but, under `--path`, walks targets from the filesystem:

```
src/os/tools/log/log_viewer.spl:4: MODULE: `use os.tools.log.journal` -- no src file provides this module
src/os/tools/log/log_viewer.spl:4: SYMBOL: imported name `JournalReader` is declared in no src file
src/os/tools/log/log_viewer.spl:4: SYMBOL: imported name `JournalFilter` is declared in no src file
src/os/tools/log/log_viewer.spl:4: SYMBOL: imported name `facility_name` is declared in no src file
```

## Fix applied

Added the negation following the established convention, and tracked both files:

```
!src/os/tools/log/
```

```
git add src/os/tools/log/journal.spl src/os/tools/log/log_viewer.spl
```

All 4 dangling-reference findings cleared (83 ← 87 for `src/os` + `src/unit`).

`dangling_reference_checker_symlink_and_untracked_blind_spots_2026-07-28.md`
describes the checker-side view of this ("Class 2 — provider exists but is
untracked"). That doc treats untrackedness as a checker false positive; here the
untrackedness was itself the defect — the provider was *supposed* to be tracked
and an over-broad ignore rule prevented it.

## Follow-up (not done here)

The blanket `log/` rule should be anchored to the build output locations it was
meant for (e.g. `/log/`, `build/**/log/`) rather than carrying an ever-growing
allowlist of source directories. Until then, **any** new source directory named
`log` will be silently dropped from git the moment it is created. A pre-commit
guard that fails when a tracked directory's sibling `.spl` files are ignored
would catch the next occurrence.
