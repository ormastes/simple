# Bug: `std.spec` `it` block only reports the LAST `expect()`/assertion, silently masking earlier failures

**Date:** 2026-07-03
**Severity:** P0 — trust: the per-`it` ✓/✗ marker (the thing agents are told to
grep for as the trustworthy signal under the interpreter-mode greenwash
caveat) is itself unreliable whenever an `it` block contains more than one
`expect()`/`assert_*` call
**Status:** RESOLVED (2026-09-02) — `_execute_it` in `src/lib/nogc_sync_mut/spec.spl`
now accumulates failures in a `current_test_errors` array (`.clear()`-ed once per
`it`, appended to by every failing `expect`/`assert_*` via `fail_assertion`,
never overwritten) instead of the single overwriting scalar this bug
describes. The reported outcome is `current_test_errors.len() == 0`, so one
failure anywhere in the block flips the whole block to FAILED and is not
erased by a later passing call.

**Verification (2026-09-02):** reproduced the bug's exact repro
(`expect(1).to_equal(2)` followed by `expect(3).to_equal(3)` in one `it`
block) via `bin/release/aarch64-apple-darwin/simple_seed run` against current
source. Output:
```
✗ fail then pass in same it-block MUST FAIL
  expected 1 to equal 2
3 examples, 2 failures
```
Current source reports FAILED with the FIRST failure's message retained —
the opposite of the bug's original repro (`✓ ... / 1 example, 0 failures`).
Also re-read `_stable_expect_helper`/`_expect_begin_matcher`
(`src/lib/nogc_sync_mut/spec.spl:711-756`), which shows a later, more
targeted fix for a closely related defect
(`doc/08_tracking/bug/bare_expect_statement_vacuous_2026-08-18.md`) already
landed on top of the accumulating-array design this bug asked for — so this
is not a coincidental pass but the documented result of that later work.

Regression guard added:
`test/01_unit/lib/std/spec/it_block_error_accumulation_spec.spl` (spawns
`test/fixture/spec/it_block_last_expect_wins_fixture.spl` as a real child
process via `capture_exec` and asserts on its real stdout, since
`current_test_errors` is module-private and not otherwise observable from an
external spec). The fixture itself was directly verified against the current
`nogc_sync_mut` implementation as shown above; running the guard spec through
the standard `bin/simple test`/`bin/simple run` entry point could not be
confirmed on this host because the deployed `bin/simple` here is a stale
build that does not parse current colon-block `describe`/`it` syntax at all
(unrelated pre-existing environment issue, not specific to this fix — see the
PR that closed this record for the full toolchain-state note).

Not verified: the `gc_sync_mut`/`gc_async_mut`/`nogc_async_mut` sibling
`spec.spl` variants were not independently re-read for this closure; the
`nogc_sync_mut` variant is the one this record and its guard spec exercise.
Nested `describe`/`context` framing remains unverified per the bug's own
"Follow-up" section.

---
**Original filing (2026-07-03), retained for history:**
Status was: Open — mitigated in new specs by using a single combined
assertion per `it` block; no interpreter fix yet

## Summary

`std.spec`'s `it(name, block)` runs `block()` and then reports `✓`/`✗` (and,
on failure, the error message) based on a module-level `current_test_error`
variable that each `expect()`/`assert_*` call **overwrites** — a passing
call clears it, a failing call sets it — with no accumulation. Only the
**last** assertion executed in the `it` block determines the reported
outcome. Every earlier assertion's pass/fail result (and failure message) is
discarded.

This means: `expect(1).to_equal(2)` (fails) followed later in the same `it`
by `expect(3).to_equal(3)` (passes) reports `✓` for the whole test — the
first, real failure vanishes with no trace, not even in the failure message.

## Reproduction

```spl
use std.spec.*

describe "sabotage check":
    it "fail then pass in same it-block":
        expect(1).to_equal(2)
        expect(3).to_equal(3)
```

Output (via `bin/simple run`, the recommended workaround for the *other*,
already-tracked aggregation greenwash —
`test_runner_interpreter_file_summary_greenwash_2026-07-03.md`):

```
sabotage check
  ✓ fail then pass in same it-block

1 example, 0 failures
```

Reversing the order (fail last) correctly reports `✗` with the failing
message — confirming "last call wins," not "first failure wins" or
"any failure wins."

## Why this matters beyond the obvious

The project's own documented workaround for interpreter-mode test-runner
greenwash is: *"run the same assertions through a `bin/simple run …` harness
… per-block output shows the red ✗ marks the aggregate drops"* (spipe skill,
`doc/08_tracking/bug/test_runner_interpreter_file_summary_greenwash_2026-07-03.md`).
That advice assumes the per-`it` ✗ marker itself is trustworthy. This bug
shows it is **not**, once an `it` block has more than one assertion and a
later one happens to pass — which is the common case for any BDD-style test
with multiple `step()`-separated checks in one scenario (the exact shape
encouraged by the SPipe scenario-manual style: `step("...")` /
`expect(...)` pairs, several per `it`).

## Real-world impact found this session

`test/02_integration/app/spritesheet/spritesheet_cli_spec.spl`'s "packs 2
fixture PNGs..." `it` block asserts ~15 things (manifest fields, atlas
regions, 8 individual pixel values). A deliberately sabotaged early pixel
assertion (`expect(img.pixels[...]).to_equal(0xDEADBEEFu32)` instead of the
correct source pixel) was silently swallowed because later pixel assertions
in the same block passed — the block still reported `✓`.

## Mitigation applied

Restructured that spec so each `it` block computes a single combined
boolean (or otherwise ensures the last statement's outcome represents the
whole block) rather than relying on N independent `expect()` calls whose
individual results are discarded except the last. This is a spec-authoring
workaround, not a fix — it only helps specs written after this was known.

## Real fix needed

`std.spec`'s `_execute_it`/`fail_assertion` (see
`src/lib/nogc_sync_mut/spec.spl` and its `gc_async_mut` /`gc_sync_mut`/
`nogc_async_mut` siblings) must **accumulate** failures across an `it`
block (e.g., append to a list, or latch `current_test_error` to the first
failure and never overwrite it with a later pass), not overwrite on every
call. Until fixed, every existing multi-assertion `it` block in the
repository is a candidate for the same silent-masking failure mode — this
is a strictly bigger blast radius than the already-tracked aggregate
file-summary bug and should be prioritized accordingly.

## Follow-up

- Audit whether this also affects `context`/nested `describe` framing (not
  tested here — only a flat `it` block was reproduced).
- Consider a lint/spec-authoring rule: an `it` block should either contain
  exactly one meaningful `expect()`/`assert_*`, or explicitly combine
  multiple checks into one boolean before the final assertion, until the
  runner itself accumulates failures correctly.
