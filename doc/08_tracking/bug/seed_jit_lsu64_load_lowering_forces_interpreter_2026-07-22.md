# Bug: seed JIT HIR lowering fails on lsu64_load (valid cross-module import) — forces interpreter, blocks OpenSBI banner

- **ID:** seed_jit_lsu64_load_lowering_forces_interpreter
- **Date:** 2026-07-22
- **Status:** OPEN (Rust seed-side; cannot be fixed in pure Simple)
- **Severity:** high — it is the throughput blocker to the OpenSBI banner / Linux-on-SoC bring-up
- **Component:** seed JIT HIR lowering (`src/compiler_rust`), not the .spl compiler

## Symptom
Every `bin/simple run` of the RV64 SoC probes prints:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
Unknown variable: lsu64_load while lowering core64_combinational
```

`lsu64_load` is defined and exported (`src/lib/hardware/rv64gc_rtl/lsu.spl`),
resolves fine in the interpreter, and every other cross-module symbol in the
same function lowers — only this import trips the JIT. (Same class previously
seen with `OP_MISC_MEM`, which was a genuinely-missing constant, since fixed;
`lsu64_load` is NOT missing — the import is valid.)

## Impact
`core64_combinational` is the hottest function in the RV64 SoC model. The JIT
fallback pins the whole SoC sim to the interpreter at ~600 ticks/s. Booting
real OpenSBI to its console-init / banner (empirically far past 300k datapath
ticks) is impractical per process at that speed — see
`rv64_opensbi_fw_platform_init_throughput_frontier_2026-07-22.md`. Fixing this
lowering bug is the single highest-leverage lever to reach the OpenSBI banner
and, beyond it, a Linux console.

## Evidence the banner is gated here, not on DTB placement
Reviewer diagnostic (2026-07-22), honest 128 MiB map, watchdog defeated
(`SIMPLE_TIMEOUT_SECONDS=0`), two DTB placements:
- A: a1=0x80060000 (dtb@0x60000, inside OpenSBI's ~323 KB image) — 200k ticks,
  `uart_len=0`, console-init funcs never reached.
- B: a1=0x87F00000 (dtb relocated near top of 128 MiB, clear of firmware) —
  **identical**: 200k ticks, `uart_len=0`, console-init funcs never reached.
DTB relocation changes nothing at 200k ticks; the boot simply has not executed
far enough to reach `uart8250_init`/console registration. The bound is ticks
(hence JIT speed), not DTB correctness (though the DTB match should still be
verified once the boot runs deep enough).

## Repro
`bin/simple run test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl 2>&1 | grep lsu64_load`

## Fix direction (Rust seed)
The JIT HIR lowering symbol table for a function body must resolve imported
functions the same way the interpreter does. Suspect the lowering pass only
seeds entry-module bindings (same shape as the AOP run-path entry-module-only
weaving gap). Fix in `src/compiler_rust`; then re-run the honest-map OpenSBI
boot — with JIT speed it should reach console init in a single process, at
which point verify the ns16550a DTB node matches the UART MMIO and capture the
banner bytes.

## Cross-refs
[[rv64_opensbi_fw_platform_init_throughput_frontier]] — the banner frontier doc
whose CORRECTION section this bug now anchors.
