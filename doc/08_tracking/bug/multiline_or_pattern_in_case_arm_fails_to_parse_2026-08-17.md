# A multi-line or-pattern in a `case` arm does not parse

Status: **FIXED** (verified 2026-08-17 on the seed rebuilt that day; was P2)
**Found:** 2026-08-17 while unblocking `check-native-trailing-default-param` on main

## Symptom

An or-pattern continued across lines via a trailing `|` fails to parse:

```
error: compile failed: parse: Unexpected token: expected pattern, found Indent
```

The continuation line is lexed as an `Indent` token, and the pattern parser has
no rule for it, so it reports "expected pattern, found Indent".

## Minimal reproduction (both verified)

FAILS -- rc=1:
```
    match e:
        case A(x) | B(x) |
                C(x):
            x
```

PARSES -- rc=0, identical semantics:
```
    match e:
        case A(x) | B(x) | C(x):
            x
```

## Why this matters beyond style

It is a silent trap for wide enums. `MirTypeKind` has ~24 variants; an arm
covering all of them is far past any reasonable line length, so an author
naturally wraps it -- and gets a parse error whose message points at
indentation rather than at the wrap. The construct looks obviously valid.

This exact form landed in `src/compiler/50.mir/verification_semantic_coverage.spl`
via `d9dfcbf80e0` and made the file unparseable. Because
`check-native-trailing-default-param.shs` runs a native build over the tree,
that ONE file turned the guard RED on pristine `origin/main` and **blocked every
push repo-wide** until it was joined onto single lines. Cost: multiple lanes
spent hours diagnosing blocked pushes, and at least one push was made with
`--no-verify` to get around it.

## Workaround applied, and why it is only a workaround

The two arms in that file were joined onto single lines. Per the project rule
("when a short, safe grammar or compact expression form fails ... fix it or
record a concrete bug/feature request instead of silently normalizing the
workaround"), the workaround is NOT the resolution -- this row is the record.
The lines are now 150+ characters, which is itself undesirable.

## Fix direction

The pattern parser should skip `Indent`/`Dedent` tokens while a pattern is
syntactically incomplete -- i.e. immediately after a trailing `|`. Compare the
expression parser, which already tolerates wrapped binary operators.

## RESOLUTION (2026-08-17) — fixed, verified

The "Fix direction" below was implemented (by another lane; this row only
verifies it). Root cause fix:
`src/compiler_rust/parser/src/parser_patterns.rs:209-220`
`fn skip_newlines_and_indents_for_pattern()` — skips `Newline`/`Indent` while a
pattern is syntactically incomplete, returning the Indent count so the arm can
unwind, exactly as this row prescribed.

**Binary identity:**
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust seed, rebuilt that day).

**Command and observed output** — trailing-`|` form (the exact shape in this row):

```
$ cat r3.spl
enum E:
    A(x: i64)
    B(x: i64)
    C(x: i64)
fn f(e: E) -> i64:
    match e:
        case A(x) | B(x) |
                C(x):
            x
fn main() -> i64:
    print("{f(E.A(3))}\n")
    0
$ bin/simple run r3.spl
3
```

It not only parses but **evaluates correctly** (`3`), so the arm is not silently
truncated.

Additionally, the previously-untested **leading-`|`** continuation style (listed
under "Not proven" below) was tested here and also PASSES:

```
$ cat r3b.spl      # ... case A(x) | B(x)
                   #             | C(x):
$ bin/simple run r3b.spl
7
```

Still genuinely untested: `if val`/`let`-pattern positions.

The workaround in `src/compiler/50.mir/verification_semantic_coverage.spl`
(arms joined onto 150+ char single lines) may now be reverted to the wrapped
form; that is left to the owning lane and is not done here.

## Not proven
- Only `case` arms in `match` were tested. Whether `if val`/`let`-pattern
  positions have the same limitation is UNTESTED.
- Whether a leading-`|` continuation style parses was not tested.
- No fix attempted in the parser; the root-cause file:line in the pattern
  parser was not located.
