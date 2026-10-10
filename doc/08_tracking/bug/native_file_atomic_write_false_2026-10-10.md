# Native file_atomic_write returns false for a valid pointer write (2026-10-10)

Status: OPEN runtime/file facade defect.

A no-stub Stage 2 LLVM/core-C build of `test/fixtures/compiler/transition_atomic_native_probe.spl` linked 43 modules. In a freshly created directory, `file_atomic_write(path, "none")` returned false while `file_create_exclusive(sibling, "none")` returned true. Receipt: `build/mini_builds/item6_transition_atomic_probe_20261010/` (build exit 0, run exit 2, output `atomic=false exclusive=true`). The probe source was diagnostic and was removed after capture.

The cause is not isolated. `src/lib/nogc_sync_mut/io/file_ops.spl` calls `rt_file_atomic_write`; the native C implementation expects boxed text values. Investigate the emitted ABI and runtime dispatch before changing either contract. The Item 6 transition publisher now uses the existing exclusive-create and rename facades under its lock, which restored first-generation publication. Other atomic-write callers remain exposed until the boundary is fixed and tested.
