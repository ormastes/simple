# Pure-Simple interpreter: recycled scope slot keeps stale bucket heads, aborting the second iteration of every scoped construct

- **Filed:** 2026-09-06
- **Status:** FIXED 2026-09-06 (this record), with a regression spec.
- **Severity:** High — hard abort, not a wrong answer, but it makes the
  pure-Simple tree-walking interpreter unable to run any loop body, block or
  match arm more than once.
- **Component:** `src/compiler/10.frontend/core/interpreter/env.spl` —
  `env_push_scope` / `_reset_scope_buckets`
- **Engine:** the pure-Simple tree-walking interpreter
  (`src/compiler/10.frontend/core/interpreter/**`). Nothing to do with the Rust
  seed's own interpreter or the JIT — those have their own environment.
- **Found while:** building the executable proof requested by
  `interp_while_body_scope_leak_2026-07-15.md`. The scope-leak fix that record
  describes is real and correct; it just could not be exercised twice.

## Symptom

The second `env_define` into a scope slot that has been pushed, popped and
pushed again aborts:

```
error: semantic: array index out of bounds: index is 0 but length is 0
```

Minimal reproduction, driving `env.spl` directly (no compiler binary involved):

```
env_reset()
env_define("x", val_make_int(99))     # depth 1

env_push_scope()                      # depth 2, slot GROWN
env_define("y", val_make_int(1))      # ok
env_pop_scope()                       # depth 1

env_push_scope()                      # depth 2, slot REUSED
env_define("y", val_make_int(2))      # <-- aborts
```

Measured before the fix (instrumented `env_define`, prints removed again):

```
DBG define name=x top=0 bucket=25 head=-1 keys_len=0
d0 depth=1
d1 depth=2
DBG define name=y top=1 bucket=12 head=-1 keys_len=0
d2 y=1
d3 depth=1
d4 depth=2 (reuse path)
DBG define name=y top=1 bucket=12 head=0  keys_len=0
error: semantic: array index out of bounds: index is 0 but length is 0
```

The last line is the whole bug: on the reused slot, bucket 12 still holds the
chain head `0` from the slot's previous life, while `keys` has been cleared to
`[]`. `env_define` walks `while idx != -1: if r_keys[idx] == name` and indexes
element 0 of an empty array.

## Root cause

`env_push_scope`'s reuse path cleared three of the four parallel arrays by
assigning through the owner, but reset the fourth through a helper that took
the row **by value**:

```
fn _reset_scope_buckets(buckets: [i64]):     # not `mut` -> a snapshot
    var i: i64 = 0
    while i < buckets.len():
        buckets[i] = -1                      # written to the snapshot, discarded
        i = i + 1

fn env_push_scope():
    if env_depth < scope_hm_keys.len():
        scope_hm_keys[env_depth] = []
        scope_hm_vals[env_depth] = []
        _reset_scope_buckets(scope_hm_buckets[env_depth])   # no-op
        scope_hm_nexts[env_depth] = []
```

Arrays are value types, so a non-`mut` array parameter is a snapshot and every
write inside the helper was thrown away. The comment on the helper ("Reset all
bucket entries to -1 in-place") described the intent, not the behaviour.

The sibling code in the same file already had it right —
`env_push_frame` resets a recycled frame with
`frame_locals[frame_depth][lc] = -1`, writing through the owner, and its
comment even calls out that it avoids "a temp-alias copy of the slot array per
call". `_reset_scope_buckets` was the one place the owner-write idiom was not
applied.

## Fix

Pass the slot INDEX instead of the row, and write through the owner. The
no-allocation intent is preserved exactly — no new bucket array is built:

```
fn _reset_scope_buckets(slot: i64):
    var i: i64 = 0
    while i < scope_hm_buckets[slot].len():
        scope_hm_buckets[slot][i] = -1
        i = i + 1
```

Nothing was deleted and no behaviour was dropped: the helper still exists, is
still called from the same place, and still resets in place.

## Why nothing caught this

`env.spl`'s own unit spec (`test/01_unit/compiler_core/interpreter/env_spec.spl`
and its sibling `ops_spec.spl`) are **source-grep specs** — they call
`file_read` on the interpreter source and assert that function signatures
appear in the text. The real executable tests are present but commented out at
the bottom of those files. A spec that greps for `fn env_push_scope` cannot
observe that `env_push_scope` recycles a slot incorrectly.

## Regression spec

`test/01_unit/compiler_core/interpreter/env_scope_slot_reuse_spec.spl`
(7 `it` blocks: 2 reproduction, 5 generalization — repeated recycles, two
nesting levels, scope-stack balance, and the two OTHER readers of the same
bucket chain, `env_assign` (`env.spl:113`) and `env_lookup` (`env.spl:143`),
which walk `buckets[scope_bucket]` into the same keys array and were exposed
to the identical stale head).

Lane: `SIMPLE_TEST_RUNNER_RUST=1 bin/simple test <spec>` on the Rust seed
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59) as HOST; the SUBJECT is the pure-Simple `.spl` interpreter source, read
from the working tree on every run. No JIT or native-lane claim is made.

Measured in one tree with one binary, `git stash` toggling only `env.spl`:

```
env_scope_slot_reuse_spec.spl   defect present : Passed: 0   Failed: 7
                                fixed          : Passed: 7   Failed: 0

while_body_scope_spec.spl       defect present : Passed: 3   Failed: 3
                                fixed          : Passed: 6   Failed: 0
```

`while_body_scope_spec.spl` is the proof spec for
`interp_while_body_scope_leak_2026-07-15.md`; three of its six blocks were red
purely because of this defect, which is how it was found.

**Runner trap:** `bin/simple test` caches per spec file by mtime and not by the
source under test — `touch` the spec before every A/B measurement or the second
run reports `Skipped 1 unchanged test(s) (cached)` and a stale verdict.
