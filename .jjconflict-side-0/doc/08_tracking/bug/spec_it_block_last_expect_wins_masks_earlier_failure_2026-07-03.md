# Bug: `std.spec` `it` block only reports the LAST `expect()`/assertion, silently masking earlier failures

**Date:** 2026-07-03
**Severity:** P0 — trust: the per-`it` ✓/✗ marker (the thing agents are told to
grep for as the trustworthy signal under the interpreter-mode greenwash
caveat) is itself unreliable whenever an `it` block contains more than one
`expect()`/`assert_*` call
**Status:** Open — mitigated in new specs by using a single combined
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
