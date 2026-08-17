# Bug: Interpreter local-slot aliasing when cross-module fn receives local object arg

**ID:** interp_crossmod_local_slot_aliasing_2026-06-15
**Severity:** P1 (silent data corruption, hard to diagnose)
**Discovered:** 2026-06-15 while building deflate_typed codec

## Symptom

When a function `F` defined in a module is called multiple times across `describe` blocks in a
spec file located under `test/` (not at the project root), and `F` contains:

1. A local variable `var x = SomeType.new()` or `var x = SomeType.constructor()`, AND
2. A call to another function from the same module `G(x, ...)` passing `x` as an argument

then on the **second and subsequent calls** to `F`, the local variable `x` is **not
re-initialized** — it retains the object reference from the first call. This causes `x` to
accumulate state across calls (e.g., a ByteBuffer keeps bytes from previous call) or hold
stale bit-reader/writer position.

## Root cause (hypothesis)

The interpreter assigns local variable slots by index in the function's activation record.
When a cross-module function call passes a local as an argument, the slot is not reset on
re-entry in the `test/` execution context (different module-resolution path). Root-level specs
use a direct execution context that does reset slots correctly.

## Trigger conditions

All of the following must be true:
- Spec file is in `test/` subdirectory (not project root)
- Function `F` is defined in an imported module (not in the spec file itself)
- `F` has a local `var` initialized via a constructor call
- `F` passes that local to a cross-module helper function as an argument

## Workaround (applied in deflate_typed.spl)

Inline the cross-module helper functions directly into `F` so no local object is passed as
an argument across module boundaries. This eliminates the trigger condition.

Applied to:
- `deflate_fixed`: inlined `deflate_fixed_emit_literal(sym, w)` → eliminated `w` cross-module pass
- `inflate_fixed`: inlined `inflate_fixed_litlen_sym(r)` and `inflate_fixed_read_dist(r)` → eliminated `r` cross-module pass

## Related bugs

- `interp_array_get_index_ge1_corruption` — `[u8].get(N>=1)` pollution across describe blocks
- `interp_unit_param_keyword_collision_2026-06-13` — interpreter identifier case sensitivity

## Reproduction

```spl
# In test/any_path/probe.spl — fails on second call
use std.spec
use mymod.{MyFn}   # MyFn has: var w = BitWriter.lsb(); MyHelper(w); w.finish()

describe "A":
    it "first call":
        val result = MyFn(input1)
        assert_equal(result.len(), expected1)   # PASSES

describe "B":
    it "second call":
        val result = MyFn(input2)
        assert_equal(result.len(), expected2)   # FAILS: stale `w` from first call
```

Fix: inline `MyHelper` into `MyFn` body.
