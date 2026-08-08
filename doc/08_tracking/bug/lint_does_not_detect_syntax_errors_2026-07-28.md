# `bin/simple lint` reports "all files clean" on files that do not parse

**Status:** FIXED 2026-07-28
**Found:** 2026-07-28 (stage-4 bootstrap campaign — agent verification audit)
**Area:** `bin/simple lint` (pure-Simple source linter), `src/lib/nogc_sync_mut/tooling/`
**Severity:** high — not a wrong-output bug, a **false-assurance** bug. Lint is
widely used as the pre-landing verification gate; it cannot fulfil that role.

## Finding

`bin/simple lint` does not detect syntax errors. A file that the compiler
rejects outright passes lint with exit 0 and the message
`Lint passed: all files clean`.

## Repro

```simple
# broken.spl
fn good() -> i64:
    val x = 1
    x

fn broken( -> i64:
        val y = [1, 2
   y
```

Malformed parameter list, unbalanced `[`, and inconsistent indentation.

```
$ bin/simple lint broken.spl
[gc-warning] Higher-layer module 'std.io' (family: nogc_sync_mut) imported ...
Lint passed: all files clean
$ echo $?
0
```

Control — the compiler on the identical file:

```
$ bin/simple compile broken.spl
error: compile failed (broken.spl): parse: in "broken.spl":
  Unexpected token: expected identifier, found Arrow
$ echo $?
1
```

Note lint still emitted an unrelated `gc-warning`, so it *was* processing the
file — it did not silently skip it. It analysed a file it had failed to parse
and reported the result as clean.

## Why this matters

Lint is the cheap, fast check, so it is the one that gets run — in agent
briefings, in review loops, and by anyone iterating quickly. Treating exit 0 as
"this file is valid" is wrong in the one direction that costs the most: a file
that does not parse is reported as clean, and the breakage is discovered later,
by a bootstrap or by another session.

This was found because a verification audit of 16 seed-stdlib files was gated on
lint. The auditing agent injected a deliberate syntax error to calibrate the gate
and discovered the gate did not fire. Every "verified via lint" claim made before
that point was unfounded.

The failure mode is fail-open: the check reports success when it has not
performed the check.

## Expected

One of, in preference order:

1. Lint parses each file and reports parse errors as lint findings, exiting
   non-zero. (Best — lint becomes a real gate.)
2. Lint detects that parsing failed and exits non-zero with an explicit
   "cannot lint, file does not parse" diagnostic. (Acceptable — honest failure.)

What is NOT acceptable is the current behaviour: analyse an unparseable file and
report `all files clean`.

## Root cause (established 2026-07-28 by instrumented runs, not inspection)

The gate was already there and was already reached. `lint_cli_source()` in
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl` did:

```
parse_module_silent(content, path)
val parse_failed = parser_has_errors()
```

Instrumenting that line showed `parse_failed=false` on the repro file. Swapping
`parse_module_silent` for the non-silent `parse_module` showed the parser had
in fact emitted **six** errors on that same file:

```
[parser_error] line 5:12: expected parameter name
[parser_error] path .../broken.spl line 5:15: expected ), got Ident 'i64'
...
[lintprobe] parse_failed=false decls=5
```

So the parser detects the syntax errors correctly; the *flag* is lost.
`par_had_error` (and `par_diagnostic_emit_count`, checked the same way — it read
back `0` after six increments) is a module-level `var` in
`src/compiler/10.frontend/core/parser.spl`. Writes made to it inside the parse
call tree are not visible to a read taken after control returns across a module
boundary. Converting it to the single-element slot-array pattern the file
already uses for `par_kind_slot`/`par_line_slot` did **not** help — the whole
module-global cell is restored, not just the scalar. A value returned from the
function *does* cross correctly, and a `rt_env_set` mirror *does* survive; both
were confirmed in the same instrumented run (`local=false env=true`).

This is the same family as the interpreter place-model defects already on
record; the parser file itself carries nil-guards commented "module-level vars
may be nil in native binaries" and mirrors `par_line`/`par_col` into env vars
for exactly this reason.

## Fix

- `src/compiler/10.frontend/core/parser.spl` — added
  `parse_module_silent_checked(source, path) -> bool`, which clears a
  process-global mirror, parses, and **returns** `had_error` by value.
  `parser_error()` and `parser_expect()` additionally set the mirror
  (`par_had_error_mirror_set()`) on their existing cold error paths. Only the
  new `*_checked` entry point clears/reads the mirror, so no existing parser or
  bootstrap behaviour changes.
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl` — `lint_cli_source`
  now uses `parse_module_silent_checked()` instead of the
  `parse_module_silent` + `parser_has_errors()` pair.
- `scripts/check/check-lint-rejects-unparseable.shs` — regression guard,
  checks both directions.

**Any other caller that needs to know whether a parse failed must use the
`*_checked` form.** `parse_module_silent(...)` followed by `parser_has_errors()`
silently fails open.

## Verified

```
$ bin/simple lint broken.spl
broken.spl:1:0: error[PARSE001]: Source did not parse

Lint failed in 1 file(s)
$ echo $?
1
```

and a valid file still exits 0 with no `PARSE001`.

## Prior guidance (no longer required)

Before the fix: **`bin/simple lint` exit 0 was not proof that a file is
syntactically valid.** `bin/simple compile <file>` was the substitute, reporting
`parse:` errors and exiting 1.

Caveat when compiling a single file in isolation: unresolved imports can produce
errors pointing at unrelated files. Compare error sets BEFORE vs AFTER an edit on
the same file rather than expecting a clean run — identical error sets mean the
edit introduced nothing. Only a NEW error at or near the edit site counts.

## Related

- `doc/07_guide/infra/debugging/measurement_traps.md` — same family of defect: a
  check that appears to measure something and does not.
- `doc/07_guide/app/lint.md` — user-facing lint documentation; should carry the
  guidance above until this is fixed.
