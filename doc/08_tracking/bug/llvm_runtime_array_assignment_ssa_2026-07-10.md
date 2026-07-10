# LLVM Runtime-Array Assignment Reuses SSA Local

- **Date:** 2026-07-10
- **Status:** open
- **Area:** MIR assignment and LLVM SSA

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
