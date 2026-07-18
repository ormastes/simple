# Implicit-self field ASSIGNMENT in `me` methods silently no-ops — while the linter recommends it

**Date:** 2026-07-17
**Status:** OPEN
**Severity:** high (silent data-loss class; the tooling actively steers users into it)

## Symptom

Inside a `me` method, assigning to a field WITHOUT `self.` silently does
nothing:

```simple
class C:
    flag: bool
    me set_it():
        flag = true        # silently no-ops — self.flag stays false
    me set_it_explicit():
        self.flag = true   # works
```

Reproduced directly against the current bootstrap seed (opus review lane,
2026-07-17): implicit form leaves the field false; explicit form sets it.

## The compounding defect

The compiler prints "In Simple, 'self' is implicit in methods. Don't write
'self.'" and a lint hint recommending the implicit form — so following the
tool's own advice produces silently-broken mutation. (Field READS resolve
implicitly; ASSIGNMENTS bind a new local instead of the field.)

## Fix directions (either closes the trap)

1. Route implicit-name assignment inside methods to the field when the name
   matches a declared field (make assignment symmetric with reads), or
2. Make it a hard error / stop the lint recommending the implicit form for
   assignments specifically.

Filed per the CLAUDE.md rule: a short, safe form that fails must be fixed
or recorded, never silently worked around. Discovered as a landmine note by
the fix-guide selector lane; confirmed with a direct seed repro by the opus
review lane (see scratchpad fixguides/REVIEW.md of session 487db31f).
