# `non_exhaustive_match` offers a fix that adds a bogus arm to an exhaustive match

**Status:** OPEN 2026-09-19
**Area:** the `non_exhaustive_match` rule and its `EasyFix` generator
**Severity:** a machine-applicable fix that changes working code
**Found by:** an adversarial review of the COLL lane, on one of that lane's
  fixtures — **not a COLL defect**, but it shares the `simple fix` door

## What happens

On a `match` over an optional that already handles `Some` and `None`, the rule
reports `non_exhaustive_match` and offers a `(safe)` fix that appends

```
case _: todo()
```

The match was already exhaustive. The added arm is unreachable, and `todo()`
in it is a trap that will never be hit but will read to the next person as
unfinished work. If the arm is ever reached — because the rule is wrong about
exhaustiveness in some other direction too — it aborts.

## Worse: the applied result does not parse

The bogus arm is not the whole defect. Running a full `bin/simple fix` on the
same fixture produces a file the PARSER REJECTS:

```
error: expected Indent, found Case
```

So the rule does not merely append an unreachable arm — it emits text that is
not valid Simple, turning a working file into one that will not compile. That
is strictly worse than the bogus arm and than any of the 23 COLL cases this
lane closed: those produced wrong but parseable programs, which at least still
run. A fix whose output the parser refuses cannot be defended as a
conservative suggestion under any reading.

It also means the two halves want separate fixes. Suppressing the false
exhaustiveness verdict removes the occasion for the bad rewrite, but the
RENDERER is independently broken and would still emit unparseable text
wherever the rule does fire legitimately.

## Why it is worth filing here

This lane spent five rounds establishing that a machine-applicable fix must
PROVE its precondition before rewriting, and closed 23 measured cases where
the COLL fix did not. `non_exhaustive_match` comes through the **same
`simple fix` door** with confidence `safe`, and this instance shows the same
class of defect: a rewrite offered on a precondition the rule has not
established.

Two things follow that are bigger than one rule:

1. **The exhaustiveness check itself is wrong** on `Some`/`None`, so the
   WARNING is a false positive before any fix is considered.
2. **No audit exists of the other fix providers behind that door.** The COLL
   provider was audited to destruction; nothing says the others were. A user
   running `bin/simple fix` gets all of them at once.

## Related

- `doc/08_tracking/bug/lint_and_fix_disagree_on_analysable_files_2026-09-19.md`
  — the same door analyses files the linter cannot, so a provider there can
  act on a parse the front end never finished checking.
- `doc/08_tracking/bug/coll_certain_fix_rewrites_working_programs_wrongly_2026-09-19.md`
  — the superseded COLL record, for the shape of the audit this rule wants.

## Not reduced

Reported against a lane fixture rather than a reduced case; reproducing needs
a `match` on an optional with both arms present and `bin/simple lint` or
`bin/simple fix --dry-run` over it. Filed without a guessed minimal snippet,
for the same reason as the string-index record: a wrong repro sends the next
person down a dead end.
