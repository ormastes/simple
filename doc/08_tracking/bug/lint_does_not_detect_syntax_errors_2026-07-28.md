# `bin/simple lint` reports "all files clean" on files that do not parse

**Status:** open
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

## Guidance until fixed

**`bin/simple lint` exit 0 is not proof that a file is syntactically valid.**
Use `bin/simple compile <file>`, which reports `parse:` errors and exits 1. Keep
lint as a secondary style/family check.

Caveat when compiling a single file in isolation: unresolved imports can produce
errors pointing at unrelated files. Compare error sets BEFORE vs AFTER an edit on
the same file rather than expecting a clean run — identical error sets mean the
edit introduced nothing. Only a NEW error at or near the edit site counts.

## Related

- `doc/07_guide/infra/debugging/measurement_traps.md` — same family of defect: a
  check that appears to measure something and does not.
- `doc/07_guide/app/lint.md` — user-facing lint documentation; should carry the
  guidance above until this is fixed.
