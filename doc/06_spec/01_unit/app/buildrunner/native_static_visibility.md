# Native exported scalar visibility

Authored manual for native compiler fixtures; not generated SSpec evidence.

1. Compile `test/fixtures/buildrunner/native_const_repro.spl` with the pinned
   recovered producer and its runtime. The owner declares a private constant
   and explicitly exports it. Require the unsupported non-public imported
   static diagnostic and a nonzero compiler exit; no runnable artifact is
   accepted.
2. Compile `native_const_pub_repro.spl` with identical target, runtime, SDK,
   and resource limits. Its owner adds `pub` to the declaration. Require
   compiler exit 0, then execute the output and require exit 0. The entry
   compares the imported value to 62, so successful linkage alone is
   insufficient.

This pair documents the frozen producer boundary. It does not assert that
private exports should fail in every future compiler. A future implementation
of visibility-preserving accessors should update the expected red boundary.
Real SCV quota behavior and a full BuildRunner native build are separate gates.

3. Compile and run `scv_alloc_bounds_native_repro.spl`. Require native exits 0
   and `SCV_BOUNDS_OK`; the entry verifies five imported production values and
   actual below/above-bound responses. Retain the earlier smaller-probe run-2
   discrepancy in the bug record rather than treating instrumentation as a fix.
