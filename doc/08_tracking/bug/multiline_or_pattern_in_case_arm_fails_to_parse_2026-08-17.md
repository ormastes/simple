# A multi-line or-pattern in a `case` arm does not parse

Status: OPEN (P2)
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

## Not proven
- Only `case` arms in `match` were tested. Whether `if val`/`let`-pattern
  positions have the same limitation is UNTESTED.
- Whether a leading-`|` continuation style parses was not tested.
- No fix attempted in the parser; the root-cause file:line in the pattern
  parser was not located.
