# `cannot convert tuple to int` from a spec has no file:line

**Status:** OPEN (diagnostic quality only — the four affected specs are fixed in `4ffc3db47a9`)
**Filed:** 2026-09-03

## Symptom

A spec file with a column-0 `return ()` runs every example green and then
reports `outcome=ERROR`:

```
5 examples, 0 failures
SPEC FILE VERDICT: <path> outcome=ERROR declared>=5 executed=5 passed=5 failed=0
error: semantic: type mismatch: cannot convert tuple to int
```

The failure is real and the runner is right to fail closed: a file-scope
`return ()` returns unit from the spec script's implicit int-returning main.

## The defect being filed

The diagnostic carries **no file, no line, no column, and no source excerpt** —
just the bare sentence. With every example passing, there is nothing to point at,
so locating the one offending line took a bisect against a minimal repro rather
than reading the error. Four specs carried this for the whole life of `#149`
(`b657337c997`).

## Minimal repro (6 lines)

```
use std.spec

describe "min":
    it "works":
        expect(1).to_equal(1)

return ()
```

`bin/simple test min_a_spec.spl` -> `1 passed`, `outcome=ERROR`, the bare error.
Deleting the last line -> `outcome=OK`. Note `bin/simple run` on a similarly
shaped non-spec script does **not** reject a top-level `return ()`; only the
spec/test compile path does. Whether that leniency is intended is a second
open question.

## Ask

Attach the offending span to the `type mismatch: cannot convert tuple to int`
diagnostic on the spec compile path, so the message names the `return ()` line.

## Related

- Fix commit: `4ffc3db47a9`
- Origin: `b657337c997` (feat(spipe): search providers, #149)
