# Bug: seed JIT miscompiles cross-module `u32` const import and `as u32` val-init cast to 0

- **Filed:** 2026-07-23
- **Component:** `src/compiler_rust/` bootstrap seed — JIT (Cranelift) backend, constant evaluation
- **Severity:** Medium (Rust-seed-only; interpreter and real hardware unaffected)
- **Status:** Open

## Summary

Under the bootstrap seed's **JIT** execution mode, a top-level `val` of type
`u32` whose initializer is either (a) a reference to a `u32` constant imported
from another module, or (b) an `as u32` cast, evaluates to **0**. The
**interpreter** evaluates all of these correctly. `i64` constants are unaffected
in every form (plain literal, cross-module import, and arithmetic).

## Reproduction

```simple
# module a.spl
val SHARED_U32: u32 = 0x10000000
val SHARED_I64: i64 = 0x10000000

# module b.spl
use a.{SHARED_U32, SHARED_I64}
val FROM_U32_IMPORT: u32 = SHARED_U32          # JIT: 0        interp: 0x10000000
val FROM_I64_IMPORT: i64 = SHARED_I64          # JIT: 0x10000000 (OK)
val LOCAL_CAST:      u32 = 0x10000000 as u32   # JIT: 0        interp: 0x10000000
val I64_TO_U32_CAST: u32 = SHARED_I64 as u32   # JIT: 0        interp: 0x10000000
```

Observed with `src/compiler_rust/target/bootstrap/simple run` (default JIT) vs
the same file under `SIMPLE_EXECUTION_MODE=interpreter`.

## Impact

Discovered while unifying the RISC-V SoC MMIO map into
`src/lib/hardware/riscv_common/mmio_map.spl`. The rv32 Wishbone interconnect
(`wb_interconnect.spl`) uses `u32` address constants (32-bit synthesizable bus).
Deriving them from the shared map via `use ... as u32` made every base
(`UART_BASE`, `ROM_BASE`, `CLINT_BASE`, `RAM_BASE`) read **0** under JIT, which
collapses `wb_decode_address` so UART/ROM/CLINT writes no longer route — the
console goes silent. The rv64 interconnect (`wb64_interconnect.spl`, `i64`)
imports the same map cleanly because `i64` const import is JIT-safe.

## Workaround (in tree)

- `wb_interconnect.spl` keeps its `u32` bases as **same-file literals** (the
  original JIT-safe form) with a "MUST match mmio_map" comment.
- `wb64_interconnect.spl` imports the `i64` canonical values from `mmio_map.spl`.
- `rv32_mmio_map_consistency_probe.spl` (interpreter-only) asserts the rv32
  literals equal the canonical map, so the two cannot silently diverge.

## Root-cause pointer

Likely in the seed JIT's constant lowering for narrow (`u32`) global initializers
and the `as u32` truncation cast: the value appears to be dropped/zeroed rather
than truncated. `i64` globals take a different, correct path. Not reproducible in
the interpreter, so the defect is isolated to the Cranelift const-eval path in
`src/compiler_rust/`. This is seed-only and off the FPGA critical path (the
hardware model is synthesized from interpreter-verified `.spl`, never the JIT).
