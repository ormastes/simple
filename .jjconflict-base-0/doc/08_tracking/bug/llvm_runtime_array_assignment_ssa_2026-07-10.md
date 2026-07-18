# LLVM Runtime-Array Assignment Reuses SSA Local

- **Date:** 2026-07-10
- **Status:** fixed
- **Area:** MIR assignment and LLVM SSA

**Fix:** `ssa_alloca_transform_blocks` (`src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`)
rejected any function with `blocks.len() < 2` as a "fast path". A single-block
straight-line reassignment (e.g. `out = <returned runtime array>`, a multi-def
local) was therefore never slotted, and in the `SIMPLE_BOOTSTRAP` LLVM path
(`_MirToLlvm/core_codegen.spl` returns `fn_` unchanged when the alloca transform
does not apply) the duplicate `%lN` def survived. The `ssa_var_transform`
SSA-rename fallback cannot rescue it because such a local escapes (it is
returned) and its escape gate rejects it. The single-block guard is now
`blocks.len() == 0`; the existing `slotted.len() == 0` check keeps the
no-reassignment case a no-op. Regression test:
`test/01_unit/compiler/mir_opt/runtime_array_assignment_ssa_spec.spl`
(straight-line, if/else, loop, zero-iteration-loop, and no-op shapes).

Assigning a returned runtime array back to an existing variable emits a second
definition of the same LLVM local. The span probe produced:

```text
%l5 = getelementptr i8, ptr %l4, i64 0
%l5 = add i64 %l11, 0
```

Rebinding the MIR `local_map` only works for straight-line code and is unsafe
across conditionals, loops, and zero-iteration exits. The proper fix needs CFG
snapshots and phi construction, with behavioral tests for straight-line,
conditional, and loop assignments.
