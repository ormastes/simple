# `simple lint` prints "Lint passed: all files clean" for a file it just reported warnings on

- Date: 2026-09-02
- Status: OPEN (filed, not fixed — see "Why this was not fixed here")
- Severity: medium (truthfulness of the verdict line every gate greps)
- Surface: `bin/simple lint <file>` (the `src/app/io/cli_lint_commands.spl` path)

## Reproduction (measured)

Fixture (2 findings, both `Warn` level, no `Deny`):

```
extern fn rt_string_len(s: text) -> i64

fn dirty(s: text) -> i64:
    return rt_string_len(s)
```

```
$ bin/simple.exe lint <fixture>.spl
<fixture>.spl:1:11: warning[RAW-RT-001]: product code must not declare raw runtime intrinsic `rt_string_len` directly
<fixture>.spl:4:12: warning[RAW-RT-002]: product code calls raw runtime intrinsic `rt_string_len` directly

Found 0 error(s), 2 warning(s), 0 auto-fix(es) available

Lint passed: all files clean          <-- FALSE
$ echo $?   # read directly into a variable, not through a pipe
0
```

Binary: `bin/simple.exe`, md5 `d52d770724a9f8797e98ac7819709ab9`, 16,347,136 bytes,
mtime 2026-09-01 17:54 (announces itself as a bootstrap seed).

The findings are printed and the per-file count line is correct. Only the
**verdict line** is wrong — and the verdict line is the thing every consumer
greps (15 files under `scripts/` and `test/` match "Lint passed").

## Mechanism

`_run_lint_with_linter_source` (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:546`)
returns `3` for NOT-LINTED, `1` when `error_count > 0`, and `0` otherwise —
warnings do not affect the return value. `run_lint_command`
(`src/app/io/cli_lint_commands.spl:227`) therefore sees `file_exit == 0`, leaves
`failed_files` at 0 and `exit_code` at 0, and falls into the `elif exit_code == 0`
arm at `:265-271` that prints `Lint passed: all files clean`.

The sibling implementation `src/app/io/_CliCommands/run_commands.spl:336-355`
does NOT have this bug: it counts `visible_count` per file and prints
`Lint found issues in {n} file(s)`. The two lint CLI surfaces disagree.

## Why this was not fixed here

The clean fix is a warnings-only sentinel out of the shared tail
(`4` = linted, no errors, warnings reported), consumed by
`cli_lint_commands.spl` as "not a failure, but not clean either", so a clean run
keeps printing the byte-identical old string and a warned run prints
`Lint passed with <n> warning(s)`.

The blocker is that all four public entrypoints — `run_lint_file`,
`run_lint_file_with_linter`, `run_lint_source_with_linter`, and
`run_lint_source_with_linter_policy` — funnel into that one tail, and
`run_commands.spl:321` treats ANY nonzero return as "has issues" and sets
`exit_code = 1`. Introducing the sentinel therefore silently flips
`simple lint`'s EXIT CODE for warning-only files on that second surface. That is
a behaviour change to a gate-visible exit status, which needs an owner's
decision rather than a drive-by edit.

## Fix options

1. Sentinel `4` as above, plus an explicit `case 4` arm in `run_commands.spl`
   that keeps its current exit code. Smallest change; needs both call sites
   touched in one commit or the fix is half-done.
2. Return a struct (`errors`, `warnings`, `not_linted`) from the tail and adapt
   both surfaces. Cleaner, larger blast radius.
3. Converge the two lint CLI surfaces onto one implementation and delete the
   other. Correct long-term, out of scope for a verdict-line fix.

## Notes

- Do NOT "fix" this by making warnings exit non-zero without deciding option 1
  vs 2 — that changes the contract of every consumer of `simple lint`.
- Do NOT change the string `Lint passed: all files clean` for the genuinely
  clean case; 15 files grep for it.
