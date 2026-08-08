# The `dropped=` greenwash gate was silently reverted by a docs-titled commit, and the tail-expression fix widened the hole (2026-08-08)

**Status: FIXED.**

## Summary

`SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N`
is the spec runner's authoritative per-file result line. `dropped` is
`declared − executed`: examples the file **declared but never ran**. A verdict
carrying `dropped>0` is therefore *not* a clean bill of health — it is the
signature of a file that silently ran a fraction of itself.

`24cfc32db98` ("fix(test): gate the truncation-verdict bypass on dropped=0")
taught `parse_spec_file_verdict` to parse `dropped` and gated the truncation
bypass on `verdict_dropped == 0`.

**`db31e93217d` reverted all of it.** That commit's subject is
`docs(bug): pure-Simple does NOT carry the array-OOB sentinel leak; tuple index
does` — an unrelated documentation change. Alongside two `.md` files it carried
a `-25/+8` edit to `src/app/test_runner_new/test_runner_single.spl` that removed
the `dropped` variable, the `" dropped="` extraction, the 5-tuple return, the
call-site binding, and the `verdict_dropped == 0` gate. Nothing in the commit
message mentions the runner. This is a textbook stale-base clobber hidden under
a docs label.

Verified by content, not by reading diffs:

| commit | `verdict_dropped` occurrences in the runner |
|---|---|
| `24cfc32db98` (the fix) | 2 |
| `db31e93217d` (docs-titled) | **0** |
| `f9c0447dc25` (tail-expression fix) | 0 |
| `origin/main` `e85d83562f4` | **0** |

## Why the hole was *wider* than before the revert

`f9c0447dc25` (the tail-expression false-RED fix) added a **second**
verdict-trusting bypass, in the plain final `else` branch:

```
val verdict_clean = has_verdict == 1 and verdict_executed > 0 and verdict_failed == 0
val exit_code_spurious = code != 0 and verdict_clean and real_failed == 0 and ...
```

It was written against a base that already lacked the gate, so it inherited the
omission. The consequence: a spec emitting
`declared>=10 executed=1 passed=1 failed=0 dropped=9` **and** exiting nonzero
now read as fully GREEN — with no truncation required, on the ordinary path
every non-`--assert-ran` spec takes. The original bug needed a >4MB truncated
stream to reach its bypass; this one needs nothing.

Note also that `f9c0447dc25`'s own in-code justification argues the bypass is
safe because a clean verdict is "POSITIVE evidence that the process completed
and nothing failed". That argument is only sound *with* the `dropped` gate:
without it, `executed=1 declared>=10` is precisely a process that did **not**
complete its declared work.

## Fix

`src/app/test_runner_new/test_runner_single.spl`:

- `parse_spec_file_verdict` parses `" dropped="` again and returns
  `(executed, passed, failed, dropped, has_verdict)`.
- **Unknown fails closed:** a verdict line with no parseable `dropped=` yields
  `dropped = 1`, so neither bypass can accept it. (The pre-revert version left
  it at `-1`, which compares unequal to `0` and so also failed closed, but only
  by accident; this makes the intent explicit.)
- Both verdict-trusting bypasses — the truncation branch and the
  `verdict_clean` branch — require `verdict_dropped == 0`.
- The `SIMPLE_TEST_RUNNER_DEBUG` line prints `v_d={verdict_dropped}`.

## Regression control

`scripts/check/check-spec-runner-tail-expression-verdict.shs` asserts, as a
source invariant, that **every** line testing `verdict_executed > 0` also tests
`verdict_dropped == 0`, and that at least two such gates exist. A synthetic
fixture cannot reach this defect — manufacturing a real `dropped>0` verdict
requires the interpreter to drop declared examples — so the source invariant is
the only cheap control, and it is exactly the check that would have caught
`db31e93217d` at push time.

The same fence carries the runtime control for the tail-expression mechanism
(`spec_runner_describe_tail_expression_exit_code`): a passing tail-expression
spec must be GREEN, a failing one must stay RED, and the cured twin (any
statement after the block) must be unaffected.

## Process lesson

A commit whose subject says `docs(...)` reverted a landed correctness fix in a
different subsystem. `git log --oneline <file>` listed it, but nobody reads a
docs commit's diff. The generalisable guard is the one this doc adds: encode
load-bearing gates as *source invariants* in a `scripts/check/` fence, because
a fence fires on the content regardless of what the commit message claims.
