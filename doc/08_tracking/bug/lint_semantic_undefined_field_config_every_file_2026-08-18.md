# bug: `lint-cached.shs` FAILs every file with `undefined field 'config'` — non-discriminating

- Date: 2026-08-18
- Lane: lane-aspect-dynload
- Reporter: lint sweep agent

## Symptom

`sh scripts/check/lint-cached.shs <file>` returns `FAIL` with the identical
diagnostic regardless of which file is linted:

```
error: semantic: undefined field 'config': cannot access field on value of type 'object'
```

## Evidence

Two independent lint runs, on two files with no relationship to each other:

1. `src/lib/common/aspect_pack.spl` (this lane's own file, 2026-08-18 lane
   changes) — log:
   `/mnt/data/tmp/claude-1000/-mnt-data-worktrees-lane-aspect-dynload/2aaf68b2-ff6f-422e-b914-5b713d9fcf0b/scratchpad/lint1.log`
   verdict: `FAIL — 1 file(s) checked, 1 with findings`

2. `src/lib/common/base_encoding.spl` (control — long-stable, untouched by
   this lane, cited in `.claude/rules/commands.md` as the canonical
   lint-cache example file) — log:
   `/mnt/data/tmp/claude-1000/-mnt-data-worktrees-lane-aspect-dynload/2aaf68b2-ff6f-422e-b914-5b713d9fcf0b/scratchpad/lint_control.log`
   verdict: `FAIL — 1 file(s) checked, 1 with findings`

Both emit the byte-identical error text
`error: semantic: undefined field 'config': cannot access field on value of type 'object'`
with **no file:line attribution**, at the same position in the log output.

`grep -n "\.config" src/lib/common/aspect_pack.spl` returns **zero hits** —
the lane file never accesses a `.config` field, so the diagnostic cannot be
about lane code.

## Conclusion

The diagnostic is independent of the file under lint — it fires identically
on a file this lane never touched. `lint-cached.shs` is currently
non-discriminating: it FAILs on every input and therefore produces zero
usable signal repo-wide. This is a lint-tool defect, not a finding against
`aspect_pack.spl` or any other lane file.

## Attempted localisation (time-boxed, ~15 min)

Grepped for `.config` field access on loosely-typed values in the lint
implementation:

- `src/app/lint/main.spl` — only a re-export (`export use
  compiler.tools.lint._LintMain.config_and_model.*`), not a field access.
- `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:212` —
  `val file_config = resolve_lint_config(self.config, path, content)`
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:113` —
  `val config = resolve_lint_config(linter.config, path, content)`
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:406-442` —
  multiple `linter.config` / `linter.config.error` / `linter.config.set_*`
  accesses, e.g. `linter.config = LintConfig.from_sdn_file(sdn_path)` (406),
  `if linter.config.error != "":` (407-409).

These are candidate sites (`linter.config` reads/writes in
`entry_and_fixes.spl`) but none was confirmed as the actual failure site —
the lint tool's own diagnostic carries no file:line, so pinpointing the exact
statement would require instrumenting or bisecting the lint tool itself,
which is out of scope for this time-boxed pass. **Not localised** — stopping
here per time-box.

## Binary identity at time of report

```
readlink -f bin/simple -> /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
stat -c '%s %y' -> 59645008 2026-08-18 10:12:23.164167908 +0000
```
(Unchanged across the whole lint sweep — same binary before and after.)

## Impact on this lane's lint sweep

Lane lint status for `src/lib/common/aspect_pack.spl`,
`src/compiler/99.loader/segment_mapper.spl`,
`src/compiler/99.loader/smf_segment_load.spl`, and
`src/compiler/99.loader/module_loader_compat.spl` is **INCONCLUSIVE** —
blocked by this tool defect. Explicitly NOT recorded as pass or fail. No lane
source file was modified to appease this diagnostic.
