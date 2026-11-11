# `cannot convert tuple to int` from a spec has no file:line
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** SUPERSEDED 2026-11-11 — absorbed by the seed semantic-error-position
fix (commit `bdcbec5bd33d`, "fix(seed): JIT to_i32 family parity + semantic error
positions; close 4 P3 seed/interp/jit rows", row
`seed_semantic_error_missing_position_2026-11-09`, pinned by
`src/compiler_rust/compiler/tests/semantic_error_position.rs`). The interpreter
now records the enclosing statement's span at each execution-loop head and the
`semantic_with_context` factory adopts it (plus the current file) when the raise
site recorded no position, so `Value::as_int`'s
`type mismatch: cannot convert tuple to int` now renders with the offending
span on every path, including the spec compile path.

**Re-verification 2026-11-11 (runner9, worktree `simple-p3-runner9-20261111` @
`701c757a5658`, tracked seed `bin/simple.exe`):** the doc's 6-line repro was run
via `bin/simple test build/p3r9-tmp/min_return_spec.spl --mode=interpreter
--no-cache`. The diagnostic now reads
`error: semantic: build/p3r9-tmp/min_return_spec.spl:7:1: type mismatch: cannot
convert tuple to int` — file, line 7 (exactly the column-0 `return ()`), column
1. The Ask is satisfied; nothing further to fix here.

Historical status line: OPEN (diagnostic quality only — the four affected
specs are fixed in `4ffc3db47a9`)
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

