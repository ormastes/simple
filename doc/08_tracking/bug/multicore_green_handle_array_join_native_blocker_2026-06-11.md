<<<<<<< Conflict 1 of 1
%%%%%%% Changes from base to side #1
+# Multicore Green Handle Array Join Native Blocker
+
+Date: 2026-06-11
+Status: closed
+Owner: multicore-green lane
+
+## Summary
+
+Closed. Hosted-native code now keeps the reduced helper path native and returns
+the expected worker result:
+
+- a helper creates `var handles = []`
+- it appends `multicore_green_spawn(worker)`
+- it iterates `for handle in handles`
+- it calls `handle.join()`
+- native run prints `result=7`
+- native exit is `0`
+
+The root cause was seed-side, not Pure Simple API design. `var handles = []`
+was inferred with the default empty-array element type, so later indexed or
+iterated values could lose the appended handle type. The helper also crossed an
+obsolete compilability gate that forced non-range collection `for` loops through
+`InterpCall` even though MIR/codegen supports array iteration.
+
+## Fix
+
+- HIR lowering refines a local zero-length inferred array when `append(x)` or
+  `push(x)` is first seen, changing the local element type to `type(x)`.
+- Compilability no longer blanket-fallbacks non-range `for` loops to the
+  interpreter; nested unsupported constructs are still analyzed normally.
+- Cranelift struct values now use the same tagged heap-object ABI as LLVM, and
+  Cranelift field get/set masks the heap tag before field access.
+
+## Executable Evidence
+
+- `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl`
+- `cargo test -p simple-compiler test_empty_array_append_refines_indexed_element_type -- --nocapture`
+- `cargo test -p simple-compiler test_empty_handle_array_for_join_helper_compilable -- --nocapture`
+- `cargo test -p simple-compiler test_function_value_loop_return_helper_compilable -- --nocapture`
+++++++ Contents of side #2
# Multicore Green Handle Array Join Native Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The smaller direct struct-array blocker beneath hosted `multicore_green` is now
closed. The active lower current-source seed/native blocker is one layer above
that boundary:

- a helper keeps a local `MulticoreGreenHandle` array
- it appends one spawned handle
- it iterates that array
- it calls `handle.join()`
- native compile succeeds
- native run prints `result={result}`
- native exit is `12`

So the live seed/runtime bug is now pinned as hosted-native handle-array
iteration or `join()` dispatch, not generic by-value struct-array storage.

## Minimal Boundary

Current reduced probe:

```simple
use std.concurrent.multicore_green.{multicore_green_spawn, multicore_green_set_parallelism}

fn run_one() -> i64:
    var handles = []
    handles.append(multicore_green_spawn(\: 7))
    var total = 0
    for handle in handles:
        total = total + handle.join()
    total

fn main() -> i64:
    multicore_green_set_parallelism(1)
    val result = run_one()
    println("result={result}")
    if result != 7:
        return 12
    0
```

Observed native output:

```text
result={result}
EXIT=12
```

The smaller direct struct-array path is now green:

```simple
val items = [Boxed(value: 7)]
items[0].get() == 7
```

So the active lower boundary is no longer generic array storage. It is
hosted-native handle-array iteration and `join()` behavior.

## Why This Matters

This sits directly underneath the remaining resumable-stepper host-fairness
lane because that experiment still relies on local arrays of worker handles and
ordered result buffers. Until local handle-array join is correct, the higher
stepper path can still fail for the wrong reason.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl`
>>>>>>> Conflict 1 of 1 ends
