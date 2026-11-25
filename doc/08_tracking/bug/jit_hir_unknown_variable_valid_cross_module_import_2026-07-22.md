# Bug: JIT HIR lowering fails on validly-exported cross-module import (lsu64_load)

- **ID:** jit_hir_unknown_variable_valid_cross_module_import
- **Date:** 2026-07-22
- **Status:** RESOLVED — verified 2026-11-25 (see dated section below)
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

## Resolution 2026-11-25 (lane p3-bah, worktree D:\wt-p3-bah, release/1.0.0 @fcd95d41d60)

The tracked symptom is gone: JIT HIR lowering no longer fails on
`lsu64_load`. Repro command from this entry now produces **no**
`Unknown variable: lsu64_load`, no `[INFO] JIT compilation failed`
fallback line, and no `[engine-demotion]` line at all — the probe runs
to completion under the JIT.

One unrelated blocker had to be repaired first to make the probe
runnable: the probe still read architectural registers via the removed
`st.rf.regs[N]` array, but `RegFile64`
(`src/lib/hardware/rv64gc_rtl/regfile.spl`) was refactored to fixed
scalar fields `reg_0..reg_31` (a `[i64]` cannot cross a VHDL
clocked-entry port). That drift made the probe fail outright with
`error: semantic: class RegFile64 has no field named regs` — in the
interpreter too, so it was probe-vs-library drift, not a JIT defect.
The probe now uses the library's exported accessor
`regfile64_read_one(st.rf, N)` (same assertions, same expected values).

Evidence (Windows x86_64, tracked `bin/simple.exe`, `SIMPLE_LIB=src`):

```
$ SIMPLE_LIB=src bin/simple.exe run test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl
core64 pc=24 x1=42 x2=43 x6=42 mem64=42
PASS pc parked at jal self-loop 0x18
PASS x1 == 42 (poison skipped by taken bne)
PASS x2 == 43
PASS sw stored 42 to data memory
PASS lw read 42 back into x6
CORE64 PROBE: ALL PASS        (exit=0; grep for jit|fallback|demotion|lsu64: no hits)
```

Files changed: `test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl`
(accessor repair only). Status: RESOLVED.
