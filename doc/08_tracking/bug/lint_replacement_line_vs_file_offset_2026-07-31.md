# Suspected: `Replacement` offsets mixed coordinate systems (line-relative vs file-relative)

Status: **NOT REPRODUCED** (as a live defect). The mismatched code exists but sits
on a path that is dead as far as `simple fix` / `simple lint --fix` are concerned.

## Symptom claimed

`check_todo_format` in the lint checker computes `colon_pos` as a byte offset
*within the current line string*, then stores it directly into
`Replacement.start` / `Replacement.end`. Elsewhere, `FixApplicator.apply`
slices the *whole-file* source text using `Replacement.start` / `.end`. If the
same `Replacement` object flowed from one to the other, any fix on a line
other than line 1 would write at the wrong file position and corrupt the file.

## The two coordinate systems (file:line evidence)

- **Producer (line-relative offset, unconverted):**
  `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:607-642`
  (`check_todo_format`, called from `check_line` at line 472, passed `trimmed`
  — a single line of text, not the file).
  ```
  634:            val colon_pos = line.find(keyword) + keyword.len() + 1
  ...
  637:                start: colon_pos + 1,
  638:                end: colon_pos + 1,
  ```
  `line` here is one line of the file (`self.check_todo_format(path, line_num, trimmed)`
  at line 472). `colon_pos` is never added to a running line-start / byte-offset
  base — it is stored into `Replacement.start`/`.end` as-is. This *is* a
  line-relative offset masquerading as a file offset.

- **Consumer (slices whole-file source):**
  `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:136-192`
  (`FixApplicator.apply`, the stdlib copy) and its duplicate
  `src/compiler/90.tools/fix/main.spl:39-95` (the one actually wired to the
  `simple fix` CLI). Both do:
  ```
  187:                if typed_rep.start <= new_source.len() and typed_rep.end <= new_source.len():
  188:                    new_source = new_source.slice(0, typed_rep.start) + typed_rep.new_text + new_source.slice(typed_rep.end)
  ```
  `new_source`/`source` here is `sources[file]`, populated from `file_read(file)`
  — the **whole file**, not a line. So this side genuinely expects file-relative
  offsets.

  Contrast with the rules that actually feed `simple fix` today
  (`src/compiler/90.tools/fix/rules/impl_/*.spl`, `src/compiler/90.tools/fix/rules/helpers.spl`):
  every one of them tracks a running `byte_offset` accumulator across lines and
  adds it in (`ctx.byte_offset + indent`, etc.) before constructing a
  `Replacement`. That is the correct pattern; `check_todo_format` does not
  follow it.

## Why it does not reproduce as a live bug

`check_todo_format`'s `EasyFix`/`Replacement` is attached to a `Lint` value
that only ever reaches `LintResult.format()` for human-readable diagnostic
printing (`src/compiler/90.tools/lint/_LintMain/lint_checks.spl`). It is never
passed to `FixApplicator.apply`:

- `simple lint` (`src/app/io/cli_lint_commands.spl`) only *prints* lint
  results and, when it mentions fixing at all, tells the user:
  `"Use 'simple fix' to apply source changes."` (line 120). It never calls
  `FixApplicator`/`apply_fixes_to_disk` on `LintChecker`'s own `easy_fix`
  output.
- `simple fix` (`src/app/io/cli_lint_commands.spl:8`,
  `src/app/io/_CliCommands/{run_commands,handler_commands}.spl`) sources its
  fixes from `collect_fixes_from_source` →
  `compiler.tools.fix.rules.registry.check_all_rules`
  (`src/compiler/90.tools/fix/rules/registry.spl:67`), which enumerates a
  fixed list of ~13+ rule functions from `compiler.tools.fix.rules.impl_.*`.
  None of them is `check_todo_format`, and there is no T001/TODO-format rule
  registered at all.
- Repo-wide grep for `LintChecker(` (the class that owns `check_todo_format`)
  and for any other call site of `check_todo_format` found none outside
  `lint_checks.spl` itself.

So the two coordinate systems never actually meet: the only producer of a
line-relative, unconverted `Replacement` is not on the path that reaches the
whole-file-slicing consumer.

## Reproduction attempt (empirical, matches the static analysis)

Probe file with the malformed pattern on a non-first line:

```
fn one():
    val x = 1
    return x

fn two():
    # TODO: fix this later without area/priority tags
    val y = 2
    return y
```

```
$ bin/simple fix <probe>.spl --dry-run
...
No applicable fixes found for <probe>.spl
```

`simple fix` does not even flag the malformed TODO comment (T001 has no
registered fix rule), confirming the dead path — there is nothing to corrupt
because the rule never runs in the fix pipeline.

## Verdict

**NOT REPRODUCED** as a defect reachable from `simple fix` / `simple lint`.

The line-relative-offset-into-a-Replacement pattern in
`check_todo_format` (`lint_checks.spl:634-641`) is real, sloppy, and would be
a genuine corruption bug **if** it were ever wired into `FixApplicator.apply`
(e.g. if a future change adds a T001 auto-fix registration, or if
`simple lint --fix` is changed to apply `LintChecker`'s own `easy_fix`
results directly). It is left as a latent hygiene issue, not fixed here,
because:
- fixing it would mean guessing the right conversion (a running `byte_offset`
  accumulator threaded through the whole `check_line`/`check_todo_format`
  call chain, matching the pattern already used in
  `src/compiler/90.tools/fix/rules/impl_/*.spl` and
  `src/compiler/90.tools/fix/rules/helpers.spl`), and
- there is no runnable path today that would let a test prove the fix
  matters (the `Replacement` never leaves `lint_checks.spl`'s own diagnostic
  formatting), so any "fix" would be unverified per this investigation's own
  rules.

## Recommendation if this is picked up later

If `check_todo_format`'s fix is ever wired into an applying path, thread a
running byte-offset base (see `helpers.spl:byte_offset_of` /
`line_start_offset`, or the `ctx.byte_offset` accumulator pattern used
throughout `rules/impl_/*.spl`) through to `check_todo_format` and add it to
`colon_pos` before constructing the `Replacement`. Add a spec under
`test/01_unit/` with a multi-line fixture (TODO not on line 1) asserting the
post-fix file content, mirroring the existing `impl_/*.spl` rules' tests.
