# `case` is reserved everywhere, so `for case in …` kills the whole file at parse

**Status:** OPEN (grammar); the one spec it was blocking has been unblocked
**Found:** 2026-08-04
**Severity:** medium — a parse error rejects the entire file, so one loop
variable cost every example in it, and `case` is not on the documented
reserved-word list

## Symptom

```sh
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/01_unit/lib/common/encoding/sfnt_spec.spl
error: compile failed: parse: in ".../sfnt_spec.spl":
       Unexpected token: expected pattern, found Case
Results: 1 total, 0 passed, 1 failed
```

The offending line was an ordinary `for` loop over a list of test scenarios:

```
for case in cases:
    val result = validate_default_glyf_font(case.1)
```

Expected: `case` binds like any other name outside a `match`. Actual: the
parser reaches `for`, expects a pattern, sees the `Case` token, and aborts —
taking all four examples in the 229-line file with it.

## Root cause

`case` is lexed as a keyword unconditionally, not as a soft keyword valid only
in `match` arm position. Nothing about `for <binding> in` is ambiguous with a
match arm: `case` in a binding position cannot be anything but an identifier,
because a match arm can only appear inside a `match` block.

The reserved-word list in `.claude/rules/language.md` reads:

> **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`,
> `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`

`case` is not on it. So either the list is stale, or `case` is over-reserved —
and the diagnostic ("expected pattern, found Case") describes the parser's
internal state rather than telling the author that `case` cannot be a variable
name, which is what they need to know.

This is the same shape as `literal`, already filed as a silent soft-keyword.
The difference is the blast radius: `literal` misparses an expression, while
this one fails the compilation unit.

## What was changed

The loop variable in `sfnt_spec.spl:147` was renamed `case` → `scenario`, with
a comment pointing here. That took the file from `0 passed, 1 failed` to
`3 passed, 1 failed` — the parse error had been masking four real examples.

Per the repo rule ("when a short, safe grammar form fails … fix it or record a
concrete bug/feature request instead of silently normalizing the workaround"),
the rename is recorded here rather than left as an unexplained edit. The
grammar itself is untouched.

## Newly exposed, not yet diagnosed

With the file parsing, one of its four examples fails on real behaviour:

```
✗ matches preferred bounded Windows English names and rejects malformed records
  expected subject to be truthy, got false
```

That example (`sfnt_spec.spl:180-221`) makes roughly fifteen unlabelled
assertions against `sfnt_manifest_names_match` in a single `it`, covering
preferred-family (name IDs 16/17) precedence, lone-surrogate rejection,
truncated and odd-length name records, early storage offsets, and duplicate
ID conflicts. The runner reports only "expected subject to be truthy, got
false" with no indication of which assertion, because none of them carry a
message. Splitting that example into one `it` per property is a prerequisite
for diagnosing it, and is worth doing regardless.

## Why the grammar is not fixed here

Changing which tokens the lexer reserves affects every file in the tree and
belongs with the parser work already in flight (`parser_framework`), not in a
test-repair lane. The narrow fix — treat `case` as a soft keyword recognised
only in match-arm position — is the same change `literal` needs, so the two
should land together.

## Re-triage 2026-08-08 — STILL REPRODUCES; and it is BOTH front ends, not one

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` (Rust
bootstrap-seed banner).

Standalone repro, no spec file involved:

```simple
fn main():
    var t = 0
    for case in [1, 2, 3]:
        t = t + case
    print "sum={t}"
main()
```

    error: compile failed: parse: Unexpected token: expected pattern, found Case

Identical to the 2026-08-04 transcript, so nothing has changed. Note the JIT
does not even get to try — it reports `JIT compilation failed, falling back to
interpreter: module load error: parse: ... expected pattern, found Case`, and
the interpreter then fails on the same parse. A parse error is engine-agnostic,
which is why this one reproduces everywhere.

**New fact worth recording, because it changes the scope estimate.** The report
above attributes the reservation to the seed lexer. It is a hard keyword in the
**pure-Simple** front end as well — `KwCase` is a distinct token kind in
`src/compiler/10.frontend` (token-kind table entry `KwCase  # case`, and it
appears in the keyword group alongside `KwIf | KwElse | KwElif | KwMatch |
KwFor | KwWhile`). So the soft-keyword change has to land in both front ends to
actually free the identifier; fixing only one leaves the other rejecting the
same file. That is a further argument for landing it with the `parser_framework`
work rather than as a drive-by.

**Secondary finding confirmed:** the reserved-word list in
`.claude/rules/language.md` still reads `gen`, `val`, `def`, `exists`, `actor`,
`assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn` — `case` is not on
it, and neither is `match`, `literal`, or the other hard keywords the lexer
actually reserves. The list is not a list of reserved words; it is a list of
*surprising* reserved words that has fallen out of date. Until the soft-keyword
change lands, `case` belongs on it, since being absent from that list is what
made this cost a whole file.

**Not fixed here** (unchanged from the original disposition): the grammar is
untouched, and the rename in `sfnt_spec.spl:147` remains the only mitigation.
