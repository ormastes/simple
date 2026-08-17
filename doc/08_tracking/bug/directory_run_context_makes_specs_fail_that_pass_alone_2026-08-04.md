# A spec that passes 28/28 alone reports 3 failures inside a directory run

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
wrong; the real cause was the `T?`-to-`bool` coercion defect plus an unpinned,
concurrently-mutated working copy. Kept for the durable measurement-methodology
finding at the bottom (pin a worktree before measuring).
**Found:** 2026-08-04, while verifying the `T?`-to-`bool` coercion fix.
**Class:** measurement defect — inflates every directory-scoped failure count by
an unknown amount. Same binary, same flags, different answer.

## Symptom

`test/03_system/core/edge_case/edge_case_11_system_spec.spl`, unmodified binary,
identical flags (`SIMPLE_TIMEOUT_SECONDS=0 ... --no-cache --no-cover-check`):

| invocation | result |
|---|---|
| the file alone | `Results: 28 total, 28 passed, 0 failed` |
| inside `bin/simple test <its directory>` | `25 passed, 3 failed` |

The directory run reports the same file as red. Nothing about the file changed.

## The failures are not assertion mismatches

Across the whole `edge_case` directory run (1400 examples, 149 failed) there are
**zero** `expected ... to equal ...` lines. Every failing file carries the same
shape:

```
  FAIL  test/03_system/core/edge_case/edge_case_10_system_spec.spl (26 passed, 2 failed, 1457ms)
        Error: Process exited with code N
```

50 occurrences of `Error: Process exited with code N` in one directory run. The
spec process exits non-zero; the runner attributes that to individual examples.

## Why this matters more than the count itself

This artifact is invisible to the usual review: a directory run produces a
plausible-looking per-file `N passed, M failed` breakdown, so the numbers read
as real assertion failures. They are not. Any triage that greps the failing
files for a suspicious idiom and attributes the count to it will produce a
confident but wrong root cause — that is exactly what happened in
`optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`,
which attributed 249 of 249 `03_system/core` failures (and ~1,200 corpus-wide)
to a coercion gap whose fix moves the directory count by **zero**.

## Reproduce

```bash
F=test/03_system/core/edge_case/edge_case_11_system_spec.spl
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check $F      # 28/28 green
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check $(dirname $F) \
  > /tmp/dir.log 2>&1
grep -a 'edge_case_11' /tmp/dir.log        # 25 passed, 3 failed
grep -ac 'Process exited with code' /tmp/dir.log
```

## Not yet determined

Which cross-spec state leaks. Candidates worth eliminating in order: shared
per-run temp/fixture paths colliding between specs in one session; the resource
governor or a per-process limit tripping only under the accumulated load of a
directory run; and shared module/global state surviving between specs in the
same runner process. The `slow_it` examples are over-represented among the
failures, which points at time or resource budget rather than logic.

## Consequence for anyone measuring

Per-directory failure counts are an UPPER bound, not a measurement. Confirm a
failure per-spec before attributing it to a cause. A sibling lane independently
validated a per-spec harness against the official runner and got an exact match
(146 examples, 13 failures both ways), so per-spec measurement is available and
trustworthy where directory runs are not.

---

# RETRACTED 2026-08-04 (same day) — WRONG DIAGNOSIS. Not a directory-run defect.

**Status: RETRACTED — do not act on this report.**

The premise was that a spec passes alone and fails inside a directory run. That
comparison was invalid: the two runs were taken minutes apart in a working copy
that parallel sessions were rewriting, and `bin/simple test` **interprets
`src/lib/**` and the spec library from source**. The variable was the tree
state, not the directory.

Proof the premise is false: the same file, same command, same binary, run twice
in a row in the mutable tree gave `25 passed / 3 failed`, and later `28 passed /
0 failed`. No directory was involved in either.

Re-measured in a worktree pinned to a fixed commit (`14b0b036363`):

| binary | `edge_case_11_system_spec.spl` alone |
|---|---|
| deployed (no fix) | 25 passed, **3 failed** |
| seed rebuilt with `present_value_as_bool_arg` | **28 passed, 0 failed** |

The failures are the `T?`-to-`bool` coercion defect and nothing else — see
`optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`,
whose original diagnosis was correct. `Error: Process exited with code 1` is
simply how the runner surfaces a child spec exiting non-zero after real
assertion failures; it is not evidence of cross-spec interference.

## The one durable finding worth keeping

Measurement in this repository is **not reproducible in the shared working
copy**. Because the runner and the standard library are interpreted from source,
any concurrent session's push or rebase silently changes test results. Pin a
worktree before measuring anything:

```bash
git worktree add --detach /tmp/pinned $(git ls-remote origin main | cut -f1)
```

That, not the directory-run theory, is the lesson from this file.
