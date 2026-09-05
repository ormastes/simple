# `simple lint` prints "Lint passed: all files clean" for a file it just reported warnings on

- Date: 2026-09-02
- Status: RESOLVED 2026-09-02 (see "Resolution 2026-09-02" at the end)
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


---

## Resolution 2026-09-02

Fixed. Measured with `bin/simple.exe`
(md5 `d52d770724a9f8797e98ac7819709ab9`, 16,347,136 bytes, 2026-09-01 17:54).
Exit status taken directly into a shell variable, never through a pipe.

### Before

```
warning[RAW-RT-001]: product code must not declare raw runtime intrinsic
                     `rt_string_len` directly
Found 0 error(s), 1 warning(s), 0 auto-fix(es) available

Lint passed: all files clean          <- rc=0, and false
```

### After

```
warning[RAW-RT-001]: ... rt_string_len ...
Found 0 error(s), 1 warning(s), 0 auto-fix(es) available

Lint passed: 0 error(s), 1 warning(s) in 1 file(s)    <- rc=0, and true
```

A genuinely clean file still prints the exact byte string
`Lint passed: all files clean` at rc=0.

### Exit semantics — deliberately UNCHANGED, and why

Warnings continue to exit 0. This is the correct call, not an omission:

- It is standard linter behaviour, and `--deny-all` already exists for lanes
  that want warnings fatal.
- The `run_lint_file` sentinel ("returns 0 when the file is clean, or only
  warnings unless `--deny-all`") is read by a **second CLI surface**,
  `src/app/io/_CliCommands/run_commands.spl:321`, which turns any non-zero into
  `exit_code = 1` plus `lint: <file> has issues`. Flipping the sentinel would
  have silently made warnings fatal there too — the trap this record already
  warned about.
- Repository gates are calibrated to it
  (`scripts/check/check-pure-simple-lint-runnable.shs`,
  `check-bootstrap-essential-tools-smoke.shs`,
  `scripts/bootstrap/stage4-tooling-matrix.shs:1361`).

The defect was the verdict TEXT claiming "clean" over printed findings, and only
that was changed.

### Fix

Counts are carried out of the lint engine **without touching any return value**
(diff confirms zero changed `return` statements in `entry_and_fixes.spl`):

- `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` — `class Linter`
  gains `last_error_count: i64` / `last_warning_count: i64`. `Linter` is a
  class (reference semantics), so a batch caller sees the writes.
- `src/compiler/90.tools/lint/_LintMain/lint_checks.spl` — constructor
  initialises both to 0.
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl` — resets both at
  the top of `_run_lint_with_linter_source` (so a run that bails before analysis
  cannot leak the previous file's counts), and publishes them at the same site
  that prints `Found N error(s), M warning(s)`.
- `src/app/io/cli_lint_commands.spl` — accumulates `warning_findings` /
  `files_with_warnings` per file and prints the truthful verdict. The JSON
  summary gained `warnings` and `files_with_warnings` for the same reason.

### `run_commands.spl:321` surface: confirmed unaffected

Static verification, which is decisive here: `run_lint_file` ->
`run_lint_file_with_linter` -> `_run_lint_with_linter_source`, and no return
statement on that chain changed (`git diff -U0 | grep '^[+-].*return'` yields
only a comment line). `cli_run_lint` never reads the two new fields. A runtime
probe of that surface was attempted twice and timed out loading the `app.io`
import graph; it is not needed for the claim.

### Knock-on effect, stated rather than hidden

`scripts/check/lint-cached.shs` caches CLEAN verdicts by matching the closing
line. A warnings-only file no longer matches `Lint passed: all files clean` and
so is no longer cached as clean. That is the bug being fixed, not a regression:
it was previously caching files with real findings as clean.

### Specs

- Reproducing: `test/01_unit/app/lint_verdict_truthfulness_spec.spl` (5/5 green)
- Generalizing: `test/01_unit/app/lint_verdict_no_vacuous_pass_spec.spl`
  (4/4 green) — probes the adjacent "summary over-claims what it verified"
  family on BOTH lint CLI surfaces, and pins the unchanged sentinel.

### Cross-platform

Pure `.spl`, no path handling, no OS branch, no filesystem predicate. Behaviour
is identical on Unix; only the verdict string for warnings-only runs changes,
and only there.

### Residual — the SECOND lint surface still lies (scoped out, not fixed)

`src/app/io/_CliCommands/run_commands.spl:355` prints the identical
`Lint passed: all files clean`, and on a warnings-only file it still reaches
that line: the engine prints `warning[...]` + `Found 0 error(s), 1 warning(s)`,
`run_lint_file` returns 0 (the sentinel deliberately preserved above),
`visible_count == 0` so the loop prints `lint: <file> OK`, `total_warnings`
stays 0, and the closing verdict claims clean. Reached via `simple build lint`.

That surface cannot read the new counts as written: `run_lint_file`
(`entry_and_fixes.spl:519-522`) constructs and discards its own `Linter`
internally, so the fields are gone before it returns. Fixing it means hoisting a
caller-owned session and switching the loop to `run_lint_file_with_linter`,
which also changes the line
`val visible_count = run_lint_file(file_path, args)` that
`test/01_unit/app/lint_verdict_no_vacuous_pass_spec.spl` currently pins verbatim
— that spec assertion must be updated in the same change.

This record is therefore RESOLVED **for the `cli_lint_commands` surface named in
its header only**. The residual is stated here rather than left for someone to
rediscover from a green verdict on the wrong entry point.

### Deny path re-verified after the change (2026-09-02)

```
$ out=$(bin/simple.exe lint --deny-all dirty_lint.spl 2>&1); rc=$?
rc=1
error[RAW-RT-001]: ... rt_string_len ...
Found 1 error(s), 0 warning(s), 0 auto-fix(es) available
Lint failed in 1 file(s)
```

The `--deny-all` escape hatch cited in the exit-semantics reasoning above was
run, not merely asserted: it promotes the same finding to `error`, takes the
`failed_files` branch, and exits 1.
