# Bug: Interpreter local-slot aliasing when cross-module fn receives local object arg

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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


## 2026-08-17 CORE-P1 triage: UNPROVEN -- fix present in source, could not be executed

The COW write-back this doc needs IS present in current source: `merge_shared_collection_fields` at `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:975`, called at :1140, landed in `d8951833a74` ("container fields of a value-type struct are shared handles, not silent no-ops") and hardened by `fb065e87ab5`. It carries Array/Dict/ByteArray fields from callee back to caller and recurses through nested `Value::Object` fields, while deliberately keeping scalar and struct fields value-typed.\n\n**Reproduced RED, but the RED is not trustworthy.** A cross-module fixture (`helper.fill(b)` doing `b.items.push(7)` on a struct with an `items: [i64]` field) printed `len=0` under the deployed `bin/simple`. That binary is a RUST SEED with mtime 2026-08-16 22:59, which PREDATES the 06:39 fix -- so this RED is the expected stale-binary artifact, not evidence the defect survives.\n\nAn isolated `cargo build --release --bin simple` was started to re-test against a binary that contains the fix, and did NOT complete: the host was at load average 302-361 with 116 concurrent rustc processes. **No after-Results line was obtained. This row is an already-fixed CANDIDATE and remains UNPROVEN either way.** Re-run the fixture above against a binary built at or after `d8951833a74` to close it.


### 2026-08-18 update: DID NOT REPRODUCE against a binary containing the fix

The UNPROVEN status recorded above is now resolved. An isolated `cargo build
--release --bin simple` (own CARGO_TARGET_DIR) completed with rc 0 against a tree
containing `fb065e87ab5`, and the cross-module fixture was re-run A/B:

```
helper.spl:  struct Box: items: [i64]   /  fn fill(b: Box): b.items.push(7)
main.spl:    val b = helper.Box(items: []); helper.fill(b); print len of b.items
```

| binary | result |
|---|---|
| deployed seed (mtime 2026-08-16 22:59, predates fix) | rc 0, `len=1` |
| fresh build containing `fb065e87ab5` | rc 0, `len=1` |

Both are CORRECT (`len=1`), so the row does not reproduce. Engine was verified
rather than assumed: both runs print `[INFO] JIT compilation failed, falling back
to interpreter`, so the INTERPRETER executed the fixture -- which is precisely the
lane this bug is about. A green here is therefore not a JIT-covered false pass.

TWO HONEST CAVEATS, because the evidence is weaker than a clean A/B looks:

1. The very first run of this same fixture against the same deployed seed printed
   `len=0`; a later run of the same binary on the same fixture printed `len=1`.
   The old-seed RED was NOT reproducible run-to-run, and that flip is unexplained
   (HEAD moved deac32e -> 82cd8ee under the session while ~8 peer lanes landed,
   but this fixture exercises the Rust interpreter, not live `.spl` source, so
   that does not obviously account for it). Treat the original RED as unreliable.
2. Because the pre-fix binary also passes, this A/B does NOT isolate
   `merge_shared_collection_fields` as the thing that fixed it. What is
   established is only that the reported defect is absent from current HEAD, not
   which change removed it.
