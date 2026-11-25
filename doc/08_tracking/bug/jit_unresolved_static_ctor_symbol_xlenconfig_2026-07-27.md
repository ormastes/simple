# JIT declines whole module on unresolved static-constructor symbol `XlenConfig_dot_rv32`

- **Date:** 2026-07-27
- **Lane:** vhdl_gen RTL generation probes (`test/01_unit/lib/hardware/vhdl_gen/probe_bus_infra_gen.spl`)
- **Status:** RESOLVED 2026-11-25 — JIT unresolved-symbol demotion no longer reproduces (see verification note)

## Observation

Running the probe prints, before any test output:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
Module error: unresolved external symbol 'XlenConfig_dot_rv32' would NULL-jump in JIT;
deferring to interpreter
```

The probe then passes: all four bus-infra RTL files generate byte-identical to their
goldens, determinism included. So this is **not** a correctness failure — the fallback
works and the output is right.

`XlenConfig.rv32()` is a static constructor-style method on a struct
(`src/lib/hardware/riscv_common/xlen.spl`), called as `XlenConfig.rv32()` /
`XlenConfig.rv64()`. Cranelift cannot resolve the mangled symbol and declines the whole
module rather than that one call.

## Why it matters

1. **Perf:** one unresolved symbol demotes the entire module to the interpreter, not just
   the offending call. The vhdl_gen probes are string-heavy; interpreter-lane generation
   is materially slower than it needs to be.
2. **It changes which execution lane runs.** That is the exact mechanism recorded in
   `redeploy_gate_struct_copy_time_flip_2026-07-25.md`, where an identical binary flipped
   results because a JIT fallback (`unresolved external symbol 'rt_text_cmp_any'`) exposed
   an interpreter-only aliasing bug. Same class, different trigger: there a runtime `rt_*`
   symbol, here a **user static constructor method**. A lane that silently drops to the
   interpreter can surface interpreter-only defects in unrelated code.

## Repro

```bash
bin/simple run test/01_unit/lib/hardware/vhdl_gen/probe_bus_infra_gen.spl 2>&1 | head -3
```

## Not doing now / why

The generator lane's acceptance bar is byte-identity against silicon-proven goldens, and
that passes under the fallback. Fixing Cranelift symbol resolution for static
constructor methods is a compiler change well outside this lane. Filed rather than
normalized, per the standing rule against silently accepting a workaround.

## Suggested next step

Determine whether the mangling `Type_dot_method` is emitted for static methods but never
registered in the JIT symbol table, and whether declining per-call (instead of
per-module) is feasible so one unresolved symbol stops demoting an entire module.

## Verification 2026-11-25 (release/1.0.0, Windows host)

Reproduced against the tracked `bin/simple.exe` at `origin/release/1.0.0`
(`47d6c5eddd5`):

- `SIMPLE_LIB=src bin/simple.exe run test/01_unit/lib/hardware/vhdl_gen/probe_bus_infra_gen.spl`
  — the original `[INFO] JIT compilation failed ... unresolved external symbol
  'XlenConfig_dot_rv32'` line is **absent** (grep count 0).
- Forced the JIT lane with `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1
  SIMPLE_JIT_COVERAGE=1`: no `[jit-coverage]` de-JIT diversion line and no
  strict unresolved-symbol error — under `SIMPLE_JIT_STRICT=1` an unresolved
  `XlenConfig_dot_rv32` would have been a hard, non-zero-exit failure
  (`driver/src/exec_core.rs` propagates strict-tagged unresolved-import
  failures). The module compiles and runs on the JIT lane; the generator emits
  real RTL (`got: [library ieee;] ...`).
- Minimal direct repro (`XlenConfig.rv32()` in a 5-line script) also runs clean.

Environment limit: the probe's byte-identity comparisons FAIL in this worktree
because the sparse checkout excludes `examples/` (the silicon-proven golden
`.vhd` files read back as `""`), so `exp: []`. That is a checkout artifact of
this verification host, unrelated to the JIT symbol bug; determinism checks
PASS. The specific reported symptom (whole-module JIT demotion on
`XlenConfig_dot_rv32`) does not reproduce and is considered fixed on
release/1.0.0.
