# An `after_all` hook's write to a module global is LOST when that global was already mutated inside the same group

**Date:** 2026-08-31
**Status:** OPEN (blocks the last example of
`test/01_unit/std/spipe_before_all_after_all_spec.spl`)
**Severity:** medium (silent data-loss class; the hook runs, reads the right
value, and its write vanishes with no diagnostic)

## Context

Separate from, and uncovered by, the `after_all` drain fix in this branch.
With that fix in place `after_all` hooks DO run at the end of their group --
proven below -- but a hook's own mutation of a module-level `var` does not
always survive.

## Reproduce (Rust seed, 2026-08-31)

Write persists when nothing else mutated the global inside the group:

```simple
use std.nogc_async_mut.spipe
var marks: [text] = ["seed"]
describe "g1":
    after_all:
        marks.push("a")
    it "x":
        assert_equal(1, 1)
describe "g2":
    it "y":
        print("final len={marks.len()}")     # -> 2  CORRECT
```

Write is LOST when a `before_all` in the same group already mutated it:

```simple
use std.nogc_async_mut.spipe
var order: [text] = []
describe "g1":
    before_all:
        order.push("before_all")
    after_all:
        print("HOOK RAN len={order.len()}")  # -> 1  hook RUNS, reads correctly
        order.push("after_all")
    it "x":
        assert_equal(order.len(), 1)
describe "g2":
    it "y":
        print("final len={order.len()}")     # -> 1  WRONG, expected 2
```

The hook body executes (the print fires) and observes the *correct*
pre-mutation value, so this is not a drain-ordering or hook-registration
problem. Only the write-back is lost.

## What was ruled out

- Not the drain: `HOOK RAN` proves the hook body runs at group end.
- Not `before_all` interception. The `after_all` drain was first paired with a
  builtin `before_all` arm in `interpreter_call/bdd.rs`; removing that arm and
  letting `std.spec`'s `before_all` run the block (the pre-existing, working
  path) leaves the symptom byte-identical. `before_all` is therefore left
  unintercepted in the landed fix.
- Not group nesting: the single-writer case above uses the same drain path and
  persists correctly.

## Where to look

The hook is a closure value captured at registration time and executed later
via `exec_block_value`. Module globals reach a closure through
`captured_env_with_live_globals` / `sync_owned_captured_globals` and the
`MODULE_GLOBALS` generation counter
(`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`,
`src/compiler_rust/compiler/src/interpreter/node_exec.rs`). The likely shape is
that the earlier in-group mutation republished `order`, invalidating the owned
env template the closure captured, so the closure's write syncs back into a
template that is no longer the live global.

## Impact

`test/01_unit/std/spipe_before_all_after_all_spec.spl` reaches 2 of 3
(`before_all` both examples green; the third asserts the drained
`after_all` marker and still sees `len == 1`). Same for the third example of
`test/01_unit/std/spec_after_all_drains_at_group_end_spec.spl`, where the
inner hook's push is the earlier in-group mutation.
