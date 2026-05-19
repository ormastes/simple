# C Runtime Exclusion — State

**Date:** 2026-05-19
**Bug doc:** `doc/08_tracking/bug/c_runtime_exclusion_analysis_2026-05-18.md`

## Bug Doc Findings

The bug doc is a C-file removal audit, not a linker defect report. It lists which
`src/runtime/*.c` files have been deleted (zero callers) and which cannot yet be
removed (active Rust/codegen callers). No linker regression is described.

## Real Linker Bug Found (Different From Doc)

While tracing the code path, a distinct freestanding-routing bug was found in
`link_objects()` in `linker.rs`:

```rust
let is_freestanding = self.config.target.is_some()   // BUG: too broad
    || cross_target.os == TargetOS::None
    || cross_target.os == TargetOS::SimpleOS;
```

### Problem

`self.config.target` is set by the CLI for **any** `--target` value, including
hosted cross-compile targets such as `x86_64-unknown-linux-gnu`. The `is_some()`
clause fires unconditionally, routing the build to `link_objects_freestanding()`
even when the OS is Linux/macOS/Windows. That path emits `-nostdlib -ffreestanding
-static` and skips the C runtime archive — correct for bare-metal, wrong for
a hosted cross-compile.

### Why config.target.is_some() is redundant AND harmful

`set_target_override()` is always called alongside `config.target = Some(t)` (both
the driver CLI and native_all entry-points do this). Therefore `effective_target()`
(which powers `cross_target`) already reflects the same target. The `is_some()`
clause adds nothing for bare-metal (already caught by `TargetOS::None`) and
SimpleOS (caught by `TargetOS::SimpleOS`), but it incorrectly catches every other
cross-compile.

### Fix

Remove the `self.config.target.is_some()` clause. The two OS-based conditions are
sufficient and correct.

## Files Changed

- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` — removed
  `self.config.target.is_some()` from `is_freestanding` guard
