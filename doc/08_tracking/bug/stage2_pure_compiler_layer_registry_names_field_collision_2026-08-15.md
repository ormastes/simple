# Stage 2 pure compiler resolves `LayerDagRegistry.names` at the wrong field offset

- **Status:** source-fixed; focused Simple and rebuilt-Stage-2 verification pending
- **Date:** 2026-08-15
- **Scope:** Phase-2 tool builds and Stage-3 self-host parsing

The admitted Stage-2 compiler could not build the standalone test runner. It
loaded the 592-file closure, then exited 139 at parse `0/592`; the build log was
empty, no object was cached, and no candidate existed. The canonical Stage-3
attempt failed at the same boundary after loading 604 closure files.

The bounded LLVM replay under gdb located the fault at
`flat_ast_to_module+18427`. Disassembly shows the source loop
`for layer_name in layer_registry.names` loading offset `0x18`, which is class
field ordinal 2 plus the class header. `LayerDagRegistry.names` is ordinal 0.
`rt_for_iterable` therefore returned scalar `0x40`, and the next array-length
load faulted. This is an imported-static-factory owner-type erasure, not a
compiler convergence hash mismatch.

The minimal source repair makes the existing declared return type explicit at
the local boundary:

`var layer_registry: LayerDagRegistry = LayerDagRegistry.new()`

Evidence is retained under `build/phase2-qualification/logs/` and
`build/native_probe/stage4-owner-20260815/stage3-llvm-gdb.{log,time}`.
After manifest refresh, rebuild Stage 2 from the existing Rust authority (do
not rebuild Stage 1), rerun only the failed test-runner build with its preserved
isolated cache, run the focused source-shape spec through that runner, then
build and test the remaining essential/debug tools one at a time.
