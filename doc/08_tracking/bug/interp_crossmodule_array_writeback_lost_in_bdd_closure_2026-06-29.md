# Bug: cross-module array-arg write-back lost inside BDD it-block closures

**Date:** 2026-06-29
**Severity:** Medium-High — silently corrupts results of cross-module functions
that mutate an array parameter in place, but ONLY under the BDD test runner.
**Component:** Rust seed interpreter — function-call / closure execution
(`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs`,
`interpreter_call/core/function_exec.rs` Bug #19 write-back).
**Status:** Source fixed; execution verification pending.

## Symptom

A library function that builds a `[u8]`/`[i64]` by delegating to an in-place
append helper returns a **truncated** array when invoked from inside a BDD
`it`-block, while returning the correct array from `main()` / normal calls.

Concretely, `msgpack_encode_int(1000)` returned `[0xCD]` (1 byte) under the
spec runner but `[0xCD, 0x03, 0xE8]` (correct, 3 bytes) from `main()`.

## Minimal reproducer

```simple
# file a: lib module `m` (cross-module is required to trigger)
fn appendv(dest: [u8], src: [u8]):          # in-place mutation, no return
    var i = 0
    while i < src.len():
        dest.push(src[i])
        i = i + 1
fn build() -> [u8]:
    var r: [u8] = []
    r.push(0xCD)
    appendv(r, [3, 232])                     # mutate r in place
    r

# file b: spec
use std.spipe.*
use m.{build}
describe "x":
    it "len 3":
        expect(build().len()).to_equal(3)    # FAILS: len == 1
```

Isolation results (all via `bin/simple run`):
- `build()` from `fn main()` → 3 bytes (correct).
- Same helper inlined **same-file** in a spec it-block → correct.
- Cross-module imported `build()` from a spec it-block → **1 byte (bug)**.

So the trigger is the intersection: **cross-module call + in-place array-arg
mutation helper + BDD it-block closure**. None of the three alone triggers it.

## Suspected root

`block_execution.rs:972-974` notes the block propagates its final bindings via
`*out_env = local_env` "so callers passing a mutable env (lambda write-back)
observe argument mutations. **The throwaway-clone wrapper discards this.**"
The BDD it-block appears to invoke the imported function through a call path
that uses that throwaway-clone wrapper, so the inner helper's Bug #19 write-back
(`function_exec.rs:555`, "write back mutable-container parameters to caller's
bindings") never reaches the real caller binding. Needs tracing of which call
dispatch the it-block→imported-fn path takes vs the main→imported-fn path.

## Impact

Any cross-module encoder/serializer that appends via an in-place helper and is
covered by a BDD spec: confirmed in `encoding/msgpack`, `encoding/bson`,
`encoding/cbor` (multi-byte int/str/bin/array/map cases all truncated under the
runner). Real (non-test) usage from normal functions is unaffected.

## Workaround (landed)

Convert the append helpers from in-place mutation to **return the grown array**
and reassign at call sites (`dest = _append(dest, src)`). This removes the
write-back dependency entirely. Applied to msgpack/bson/cbor; all three specs
now 0 failures. This is the documented Simple idiom for the broader
"array-arg mutation lost in interpreter" family
(see `.claude/memory/feedback_interp_array_arg_mutation_and_run_interpret.md`).

## Proper fix

Make the it-block → cross-module call path preserve argument write-back the same
way `main()` does. This remains a fragile area (Bugs #19/#28), so execution
verification requires a seed rebuild and the focused regression pass.

## Resolution (2026-07-15)

Imported functions execute through `exec_function_with_captured_env`, which
bound and ran arguments but omitted the mutable-container write-back already
owned by ordinary function execution. That write-back is now one shared helper
called after successful ordinary and captured function bodies. It preserves
self filtering and value-struct semantics, and conservatively skips positional
reconstruction after spread or variadic binding when provenance is ambiguous.
A focused two-module BDD spec uses module-qualified calls to force the captured
function path and also covers the original imported-builder symptom.
Execution remains pending an authorized seed/runtime test run.
