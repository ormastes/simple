# `describe(...)` as the tail expression of `fn main()` leaks a constant 1 into the child exit code, manufacturing a phantom failure (2026-08-08) — FIXED

## Status

FIXED in `src/app/test_runner_new/test_runner_single.spl`. This closes the
**second, still-unexplained mechanism** left OPEN by
`spec_harness_truncated_output_false_red_2026-08-08.md`, and **corrects the
trigger** claimed by `spec_runner_fn_main_shape_exit_code_always_1_2026-08-08.md`.

## The trigger is narrower than "the `fn main()` shape"

The earlier lane blamed the `fn main():` wrapper. That is **too broad**, and the
over-broad predicate is exactly why a second lane held "entry shape" constant and
could not reproduce it.

The real trigger is **`describe(...)` (or `context(...)`) being the LAST
statement — the tail expression — of `fn main()`**. Simple returns a function's
tail expression, and for `main` that return value becomes the process exit
status. `describe(...)` evaluates to a **constant 1**, so the child exits 1.

**Adding any statement after the block cures it.** Both of these are green and
self-consistent:

```
fn main():
    describe("probe E"):
        it("passes trivially"):
            expect 1 == 1
    print "ZZ-after-describe"        # <-- cures it
```

```
fn main() -> i64:
    describe("probe F"):
        it("passes trivially"):
            expect 1 == 1
    0                                # <-- cures it
```

## It is a constant, not an example count

A 3-example spec of the triggering shape still yields `code=1`, not `code=3`
(probe G). This matters: had it been a count, exit status truncation mod 256
would make a 256-example spec exit **0** — an accidental *green*. It does not.
The failure polarity is therefore uniformly a **false RED**; no past GREEN is
suspect from this mechanism.

## Which branch fired

Not one of the three the truncation lane nominated. It is the plain final
`else` in `run_single_spec`, at the `spec failed` print (~:1007 pre-fix):

```
test-runner debug: code=1 assert_ran=false has_evidence=0 real_p=1 real_f=0
                   has_sum=0 has_v=1 v_e=1 v_p=1 v_f=0 trunc=false
```

`code=1` with `has_summary=0` drove `passed = 0`, `failed = 1` directly, and the
`if code != 0 and failed == 0: failed = 1` clamp kept it pinned. Note
`trunc=false` and a **95 KB** log — three orders of magnitude under the 4 MB
bounded-reader cap, confirming this is mechanically independent of the
truncation bug.

An extra symptom the earlier doc missed: the phantom failure is **added to** the
real passes, so the total inflates. A real repo spec with 8 passing examples
reported `Results: 9 total, 8 passed, 1 failed`.

## Ground truth

Established independently of both reported surfaces. The child was run directly
and its structured evidence file inspected: for the triggering shape the driver
writes **no evidence file at all**, while the bare shape writes
`simple-bdd-v1 / 1 / 0`. The `✓` glyph and the `SPEC FILE VERDICT` line both
report the example ran and passed. Only `Results:` and the exit code disagreed.

## The fix

In the final `else` of `run_single_spec`, the child's nonzero exit is treated as
spurious **only** when positive evidence says the run completed cleanly:

```
val verdict_clean = has_verdict == 1 and verdict_executed > 0 and verdict_failed == 0
val exit_code_spurious = code != 0 and verdict_clean and real_failed == 0 and (has_summary == 0 or summary_failed == 0)
val exit_ok = code == 0 or exit_code_spurious
```

`exit_ok` then replaces `code == 0` in the pass/fail seeding and in the final
clamp. It is placed **before** the two fail-closed clamps (`real_failed >
failed`, and the undercount clamp) so those still raise failures on top of it.

### Why this does not weaken the greenwash guards

The `SPEC FILE VERDICT` line is emitted by the driver **epilogue**, which only
runs if the spec process reaches the end normally. A spec that passes its
examples and *then* dies abnormally emits **no verdict line at all** — so the
exemption cannot fire for it. This was verified, not assumed:

```
fn main():
    describe("probe H"):
        it("passes then process dies"):
            expect 1 == 1
    exit(7)
```
→ `code=7 has_v=0` → `Results: 1 total, 0 passed, 1 failed`, **exit 1**. Correct.

The absence of the verdict line *is* the safety property. Every genuinely
nonzero exit not backed by a clean verdict, a zero ✗-glyph tally, and a
non-failing summary still fails closed. The zero-executed guard and the
truncation branch are untouched.

## Verification — six controls

| probe | shape | outcome | Results | exit |
|-------|-------|---------|---------|------|
| A | `fn main()` tail-describe | passes | 1 total, 1 passed, 0 failed | 0 |
| B | bare `describe` | passes | 1 total, 1 passed, 0 failed | 0 |
| C | `fn main()` tail-describe | fails | 1 total, 0 passed, 1 failed | 1 |
| I | bare `describe` | fails | 1 total, 0 passed, 1 failed | 1 |
| G | `fn main()` tail-describe, 3 examples | all pass | 3 total, 3 passed, 0 failed | 0 |
| H | `fn main()` tail-describe then `exit(7)` | passes then dies | 1 total, 0 passed, 1 failed | 1 |

Pre-fix, A/G/D reported `0 passed, 1 failed` + exit 1, and C/I were
indistinguishable from A/B by exit code.

Real repo spec, pre- and post-fix on the same binary and worktree
(`src/lib/nogc_sync_mut/debug/formats/test/expression_eval_spec.spl`):

```
PRE-FIX  exit=1   Results: 9 total, 8 passed, 1 failed
POST-FIX exit=0   Results: 8 total, 8 passed, 0 failed
         warning: test-runner: child exit 1 contradicted by a clean SPEC FILE VERDICT; trusting the verdict
```

### Sabotage

Restoring the pristine `origin/main` file and re-running probe A brought the
contradiction back (`exit=1`, `Results: 1 total, 0 passed, 1 failed`); restoring
the fix made it green again (`exit=0`). This also re-confirms that `.spl` edits
are live on the interpreter path with no bootstrap rebuild.

## Blast radius — corrected

The earlier doc's **133 of 22,228** counts every `^fn main()` spec file, but only
those whose `main` *ends* with the block are affected. Measured at
`origin/main` (b8cac166a1c):

- tracked `*_spec.spl`: **19,504** (not 22,228 — the tree has changed since)
- `^fn main()` shape: **133**
- **tail-`describe`/`context` in `main`: 39** — the actual blast radius

(The 39 is a static approximation: last statement at `main`'s body indentation.)

Every one of those 39 was reporting a phantom extra failure and a pinned exit 1,
so exit-status gating was vacuous for them in **both** directions.

## Note on the fix's robustness

`has_summary` is currently **0 on every run** — `parse_child_example_summary` is
effectively dead (filed separately:
`spec_runner_child_summary_scraper_returns_zero_2026-08-08.md`). The fix does not
depend on it: `has_summary == 0` falls through to verdict + glyph evidence, and
the `(has_summary == 0 or summary_failed == 0)` clause means that once the
scraper is repaired, a summary reporting real failures will still veto the
exemption.
