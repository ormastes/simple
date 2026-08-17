# RET lint does not census lambda bodies

- **Status:** OPEN (low priority — measured empty corpus)
- **Component:** `src/compiler/35.semantics/lint/return_type_mismatch.spl`
- **Filed:** 2026-08-10
- **Related:** `declared_return_type_not_enforced_2026-08-09.md`,
  `dotq_tail_position_in_bool_returning_fns_2026-08-09.md`

## Symptom

`check_return_type_mismatch` only recognises declarations matched by
`rtm_fn_header`, i.e. `[modifiers] fn NAME(` and `[modifiers] me NAME(`.
Lambda / closure bodies are never walked, so a lambda whose body disagrees
with its declared result type is invisible to both the warn phase and the
census that the promote-to-error decision depends on.

## Why it was NOT built in this pass

Measured, not assumed. An exhaustive scan of owned source for a lambda
carrying an explicit return-type annotation:

```
/usr/bin/grep -rnE "(fn\s*\(|\|[a-z_, ]*\|)\s*->" --include=*.spl src
```

returns **zero hits** across all of `src/`. Lambdas in this tree are written
`x => expr` and `x => :` block form and never declare a return type at all.

This lint compares a **declared** type against what a body yields. With no
lambda in the corpus declaring anything, adding a lambda walker would add
parser surface (multi-line `=>` blocks, nested lambdas inside call argument
lists, lambdas spanning a trailing-comma argument list) for a census
contribution that is provably 0 today. That is the wrong trade for a
warn-phase censuser whose whole design contract is "cheap, fail-quiet, never
breaks a build".

## What would make this worth doing

Either of:

1. The language gains/starts using an explicit lambda return annotation and
   the grep above stops returning zero; or
2. The lint is extended from "declared vs actual" to full inference, at which
   point lambda bodies matter regardless of annotation — but that is the type
   checker described in `declared_return_type_not_enforced_2026-08-09.md`,
   not this warn-phase text scanner.

## Acceptance criteria when picked up

- `rtm_fn_header` (or a sibling) recognises lambda forms with a declared
  result type.
- The census positive control in
  `scripts/check/census-return-type-mismatch.spl` gains at least one planted
  lambda violation that MUST fire and one correct lambda that MUST stay
  silent. A lambda walker with no silent-half control is not accepted — the
  same fail-open shape has already produced two rounds of false positives in
  this rule (`loop`/`loopback`, then `break`/`pass_`).

---

## CLOSED 2026-08-17 — WONTFIX, corpus re-measured and still empty

Re-ran the exhaustive scan the original record based its decision on, on
today's tree:

```
$ /usr/bin/grep -rnE "(fn\s*\(|\|[a-z_, ]*\|)\s*->" --include=*.spl src | wc -l
0
```

Still **zero** lambdas in owned source declare a return type, one week later.
This lint compares a *declared* type against what a body yields, so with an
empty corpus a lambda walker can only add cost and false-positive surface while
proving nothing. The decision recorded on 2026-08-10 stands and is now
re-evidenced rather than merely restated.

Reopen condition (mechanical, so this does not rot): the grep above returning a
non-zero count. Until then this is not a gap, it is a scope boundary.
