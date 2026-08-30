# Bug: JIT HIR lowering fails on validly-exported cross-module import (lsu64_load)

- **ID:** jit_hir_unknown_variable_valid_cross_module_import
- **Date:** 2026-07-22
- **Status:** OPEN
- **Severity:** medium (silent perf degradation — JIT falls back to interpreter)
- **Component:** seed JIT HIR lowering

## Symptom
Running `bin/simple run test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl`
prints:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
Unknown variable: lsu64_load while lowering core64_combinational
```

`lsu64_load` IS properly defined and exported (`src/lib/hardware/rv64gc_rtl/lsu.spl:114`)
and the interpreter resolves it fine — only the JIT's HIR lowering fails to see
the cross-module import inside `core64_combinational`.

## History
Previously masked by an earlier failure on the same function
(`Unknown variable: OP_MISC_MEM` — a genuinely missing constant, fixed by
defining/exporting OP_MISC_MEM in `rv64gc_rtl/pkg.spl`). Once that constant
existed, lowering progressed further and hit this one, which is NOT a missing
symbol: the import is valid.

## Impact
Every rv64 core probe/sim run executes `core64_combinational` (the hottest
function in the RV64 SoC model) under the interpreter instead of the JIT.
Directly relevant to the OpenSBI/Linux-on-SoC sim-throughput wall.

## Repro
`bin/simple run test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl 2>&1 | grep lsu64_load`

## Fix direction
JIT HIR lowering must resolve imported functions the same way the interpreter
does (cross-module use inside a large function body). Check whether the lowering
symbol table only carries entry-module bindings — same shape as the AOP
run-path entry-module-only weaving gap.
