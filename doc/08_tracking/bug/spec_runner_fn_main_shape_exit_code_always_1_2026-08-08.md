# Spec runner contradicts itself on `fn main()`-wrapped specs: verdict green, summary red, exit code constant 1 (2026-08-08)

## Summary

For a spec whose examples are nested inside `fn main():`, the test runner emits
**two disagreeing verdicts for the same run**, and its process exit status
carries **no information at all**:

- `SPEC FILE VERDICT` reports the truth (`passed=1 failed=0` when the example
  passes, `passed=0 failed=1` when it fails).
- The `Results:` summary line reports `0 passed, 1 failed` **regardless of
  outcome**.
- The process exits **1 whether the spec passes or fails**.

The bare `describe "...":` form (no `fn main()`) is unaffected — both surfaces
agree and the exit code is meaningful.

The practical consequence is the serious one: **for this class of spec,
exit-status gating is vacuous.** A passing spec and a deliberately failing spec
are indistinguishable by exit code. Any lane, script, or CI gate that decides
pass/fail from the runner's exit status cannot detect a real regression in these
files — it sees `1` either way.

## Severity / blast radius

- **133 of 22,228** tracked `*_spec.spl` files use the `fn main()` shape
  (`git grep -l "^fn main()" origin/main -- '*_spec.spl' | wc -l` = 133;
  `git ls-files '*_spec.spl' | wc -l` = 22228).
- Affects both `src/lib/**/test/` and `test/**` — **not** directory-dependent
  (probe D below reproduces under `test/01_unit/...`).
- Two reporting surfaces disagree, so *which* signal a lane trusts decides what
  it believes. This is worse than a merely weak oracle: it corrupts the one
  oracle everyone leans on. This session alone had already found three
  non-discriminating specs before hitting this.

## Reproduction — four probes

All four run as `bin/simple test <path>` on the deployed
`bin/release/x86_64-unknown-linux-gnu/simple`. Probe A is the original
observation; B, C, D are the discriminating controls.

### Probe A — `fn main()` shape, passing, under `src/lib/**/test/` → CONTRADICTION

```
use std.nogc_async_mut.spec.{describe, it, expect}

fn main():
    describe("probe shape"):
        it("passes trivially"):
            expect 1 == 1
```

```
SPEC FILE VERDICT: src/lib/nogc_async_mut/test/zz_probe_shape_spec.spl declared>=0 executed=1 passed=1 failed=0 dropped=0
Results: 1 total, 0 passed, 1 failed
exit=1
```

The verdict line says the single example executed and passed; the summary on the
same run says it failed.

### Probe B — bare `describe`, passing, same directory → CONSISTENT (control)

```
use std.nogc_async_mut.spec.{describe, it, expect}

describe "bare shape":
    it "passes trivially":
        expect 1 == 1
```

```
SPEC FILE VERDICT: src/lib/nogc_async_mut/test/zz_pb_spec.spl declared>=1 executed=1 passed=1 failed=0 dropped=0
Results: 1 total, 1 passed, 0 failed
exit=0
```

Same directory, same imports, same assertion. Only the wrapper shape differs.
This isolates the trigger to `fn main()`, not the location or the spec library.

### Probe C — `fn main()` shape, deliberately FAILING → both surfaces agree

```
use std.nogc_async_mut.spec.{describe, it, expect}

fn main():
    describe("fn-main shape"):
        it("fails deliberately"):
            expect 1 == 2
```

```
SPEC FILE VERDICT: src/lib/nogc_async_mut/test/zz_pc_spec.spl declared>=0 executed=1 passed=0 failed=1 dropped=0
Results: 1 total, 0 passed, 1 failed
exit=1
```

**This is the probe that identifies which number is right.** The verdict line
correctly flips to `passed=0 failed=1`, so it tracks reality in *both*
directions. The summary line and the exit code are byte-identical to probe A's —
they did not move when the outcome moved, so they carry no signal.

### Probe D — `fn main()` shape, passing, under `test/` → CONTRADICTION (rules out directory)

```
SPEC FILE VERDICT: test/01_unit/lib/nogc_async_mut/zzprobe/zz_pd_spec.spl declared>=0 executed=1 passed=1 failed=0 dropped=0
Results: 1 total, 0 passed, 1 failed
exit=1
```

## Which number is right

**The `SPEC FILE VERDICT` line is correct; the `Results:` summary and the exit
code are wrong.** Established by probe C: the verdict tracks the real outcome in
both directions, while the summary and exit code are pinned red for every
`fn main()` spec regardless of what the examples did.

So the failure mode is a **false RED on the summary/exit surface**, and —
because that surface is pinned — a **suppressed RED** for genuinely failing
specs of this shape, since a real failure looks exactly like a pass.

## Ruled out

Each of these was an earlier hypothesis in this session and was **disproved** by
the probes above:

- **Not lambda-related.** Probe A contains no lambda or closure.
- **Not `Mailbox`- or `mailbox_actor`-related.** The probes import nothing from
  those modules.
- **Not the JIT closure-ABI fallback.** The original observation was on
  `mailbox_actor_select_spec.spl`, which does log
  `JIT compilation failed ... creates a lambda/closure ... deferring to
  interpreter`. That was my own first explanation and it is **wrong** — probe A
  reproduces the contradiction with no lambda present and therefore no fallback.
- **Not directory-dependent.** Probe D reproduces under `test/`.
- **Not spec-content-dependent.** Probe A is a single `expect 1 == 1`.

## Unresolved

Not chased here: *why* the `fn main()` shape breaks the summary/exit accounting.
A likely-looking thread — stated as a lead, not a finding — is that `declared>=0`
appears for every `fn main()` spec versus `declared>=1` for the bare form,
suggesting the runner's static discovery pass does not see examples nested inside
`fn main()`, so its own expected-example accounting starts empty and the run is
booked as a failure independent of the executed results. Relevant code:
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`
(`make_result_from_structured_evidence`, `make_result_from_output`) and
`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`
(which generates `if get_exit_code() != 0: panic("test-runner: spec failed")`).
This has not been confirmed.

## How this was found

Chasing a `Failed: 1` on `src/lib/nogc_async_mut/test/mailbox_actor_select_spec.spl`
that coexisted with `executed=5 passed=5 failed=0 dropped=0`. The first control
used (a sibling spec, `test/01_unit/lib/nogc_async_mut/mailbox_spec.spl`) passed
cleanly and was wrongly read as proving the failure pre-existing-but-unrelated —
it was non-discriminating, because it happens to use the bare `describe` form.
Probe B is the control that should have been run first: same directory, same
library, differing only in the one variable under test.

---

# Second finding: a lane can "fix" a defect that exists only in uncommitted working-copy state

This is a repeatable shared-working-copy trap, not specific to the spec runner or
to `Mailbox`. Recorded here because the same investigation exposed it.

## What happened

A lane was dispatched to fix an ambiguous-export error: `Mailbox` exported from
both `src/lib/nogc_async_mut/mailbox.spl` and `mailbox_actor.spl`, with
`__init__.spl` re-exporting both. The error was real **in the working copy** and
did not exist **in the tree**:

```
git cat-file -e a019ba19aa66^:src/lib/nogc_async_mut/mailbox.spl  -> absent
git cat-file -e a019ba19aa66:src/lib/nogc_async_mut/mailbox.spl   -> absent
git cat-file -e 983058c5ff3^:src/lib/nogc_async_mut/mailbox.spl   -> PRESENT
git cat-file -e origin/main:src/lib/nogc_async_mut/mailbox.spl    -> absent
```

`mailbox.spl` was untracked at the time of the fix. A parallel session committed
it afterwards, hit the genuine ambiguity, and then deleted it as dead code
(`983058c5ff39`).

## Two consequences worth recording

1. **A lane can fix a defect that is not in the tree.** The remedy — renaming the
   tracked, facade-exported `Mailbox` to `PriorityMailbox` — churned a public API
   name to accommodate a file that was not part of the repository, and orphaned
   `actor_scheduler.spl:290` `Mailbox.new(MailboxConfig.default())`, which no
   remaining name provided. Fixed by `e7df6e011e5`.

2. **A plumbing commit built from working-copy blobs can sweep in another
   session's uncommitted edits.** Landing via
   `git hash-object -w` on working-copy files captured, alongside the intended
   change, an 8-symbol `# Re-exported from mailbox.spl` export block in
   `__init__.spl` that the committing session did not author and that referenced
   a module absent from the tree. Removed by `e7df6e011e5`.
   Blob-level anchoring protects against *losing* your edit; it does **not**
   establish that the blob contains **only** your edit. Diff each blob against
   its `origin/main` version before committing it.

## The generalizable lesson

**Enumerate against the `origin/main` tree, not the working copy.**

```
git grep -n -E '<pattern>' origin/main -- 'src/**/*.spl'
```

And remember that **relative imports are invisible to a fully-qualified-path
grep.** The original sweep searched only for `std.nogc_async_mut.mailbox` and so
could not see `actor_scheduler.spl`'s `use mailbox_actor.{Mailbox, ...}` — a
structural blind spot, not an oversight. Grep the bare type name with word
boundaries, and grep for the API *shape* (`Mailbox.new`, `MailboxConfig`) as
well as import lines.

## Related

- `doc/08_tracking/bug/stage2_mailbox_priorimailbox_rename_incomplete_blocks_build_2026-08-08.md`
  — the downstream Stage-2 breakage and its fix.
- `983058c5ff39` — deleted the dead `struct Mailbox` and its phantom facade exports.
- `e7df6e011e5` — completed the rename across `actor_scheduler.spl`.
