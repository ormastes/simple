# BUG: `wm_false_success_family_spec.spl` cannot reach a clean verdict even after all Wave-1 lanes' owned sites are fixed

- **Date:** 2026-08-05
- **Severity:** medium — blocks Task #59's stated success bar ("baseline
  drops to 0, verdict shows `failed=0 dropped=0`"), but does not indicate any
  regression in already-landed lane fixes.
- **Files:**
  - `src/lib/nogc_async_mut/wm/service.spl` (owned by wm-core / A2 scope,
    `src/lib/nogc_async_mut/wm/*.spl`)
  - `test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl`
    (owned by A0)
  - `doc/08_tracking/wm_false_success_baseline.txt`
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  lane that discovered this; see below).
- **Base for evidence:** `origin/main` = `71475ea79564d1ee4a07a339711cc0b113708483`

## Summary

After closing the last 5 owned baseline sites (`backend_webgpu.spl:12`,
`dxvk_d3d11.spl:13/13b/13c/13d`), `wm_false_success_family_spec.spl` still
cannot reach `failed=0`, for two independent reasons neither of which is
caused by, or fixable within, the closing lane's ownership:

### 1. `service.spl`'s port/window handle counters are an unbaselined predicate-4 match

`src/lib/nogc_async_mut/wm/service.spl` lines 53 and 79 (`_wm_port_ctr =
_wm_port_ctr + 1`, `_wm_window_ctr = _wm_window_ctr + 1`) match predicate 4's
regex (`_ctr \+ 1` / `\.len\(\) \+ 1`) on `origin/main` **right now**, verified
directly against the origin blob (not a locally-stale copy):

```
$ git show origin/main:src/lib/nogc_async_mut/wm/service.spl | \
    /usr/bin/grep -n -E "_ctr \+ 1|\.len\(\) \+ 1"
53:    _wm_port_ctr = _wm_port_ctr + 1
79:    _wm_window_ctr = _wm_window_ctr + 1
```

`doc/08_tracking/wm_false_success_baseline.txt` on `origin/main` has **no
line for `service.spl`** under tag 4 — only the four `dxvk_d3d11.spl` lines.
The guard spec's own comment (predicate 4's `it` block) says it "covers
service.spl's port/window counters" — implying a baseline line was expected
here but was never added. Net effect: predicate 4 has been silently RED on
`origin/main` since before this lane started, independent of the 5
`dxvk_d3d11.spl`/`backend_webgpu.spl` sites this lane owned and closed.

This is `src/lib/nogc_async_mut/wm/*.spl` — wm-core (A2) scope, not this
lane's. Needs: either an honest gate on `_wm_port_ctr`/`_wm_window_ctr`
(verify what invalidates a fabricated port/window handle, if anything, and
propagate refusal) or a documented reason it's exempt, in the same commit
that adds/updates its baseline accounting.

### 2. The guard's own non-vacuity floor (`n > 0`) makes literal baseline-zero unreachable

`wm_false_success_family_spec.spl`'s "baseline bookkeeping" example asserts:

```
val n = baseline_line_count()
expect(n > 0).to_equal(true)
```

This was written as a non-vacuity check (an empty file must not silently read
as "0 open issues" when it could mean "file unreadable"). But it also means
the file can **never** legitimately reach 0 lines while this assertion is
unmodified — even once every real predicate-tracked site is closed. Task
#59's stated success bar ("baseline line count drops to 0 ... verdict shows
failed=0") is therefore structurally unreachable without a change to this
A0-owned assertion (e.g. relax to `n >= 0` once the last real site closes, or
retire the example once the baseline is provably fully closed by some other
signal). Owned by A0 (`test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl`
is A0's, per the plan's single-writer-per-file rule) — not fixable by any
Wave-1 lane without violating the ownership split.

## Verified NOT caused by this lane's fix

With only the 5 owned sites fixed (`backend_webgpu.spl:12`,
`dxvk_d3d11.spl:13/13b/13c/13d`) and their baseline lines deleted:

```
predicate 1: GREEN
predicate 2: GREEN
predicate 3: GREEN   (was RED before this lane's fix; sabotage-verified both directions)
predicate 4: RED — "expected src/lib/nogc_async_mut/wm/service.spl to equal " (dxvk_d3d11.spl no longer appears; sabotage-verified both directions)
predicate 5: GREEN
baseline bookkeeping: RED — n=0, "expected false to equal true" (n > 0 floor)
SPEC FILE VERDICT: declared>=6 executed=6 passed=4 failed=2 dropped=0
```

Both remaining failures are attributable to files this lane does not own.

## Next step

Whichever lane owns `src/lib/nogc_async_mut/wm/service.spl` (wm-core/A2)
should close its predicate-4 gap and add its baseline accounting; whichever
lane owns `wm_false_success_family_spec.spl` (A0) should decide how the
non-vacuity floor is meant to resolve once the family is fully closed.
