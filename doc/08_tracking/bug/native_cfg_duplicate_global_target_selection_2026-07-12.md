# Native cfg duplicate global target selection

**Status (2026-07-15):** source implemented; focused AArch64/RISC-V object
regression execution remains pending.

## Evidence

An AArch64 entry-closure build of the SimpleOS PCI driver lowered the later
`@cfg(riscv64) val PCI_ECAM_BASE` value (`0x30000000`) instead of the AArch64
value (`0x4010000000`). The same target split expressed as `@cfg` functions is
selected correctly.

## Required fix

Native symbol collection must filter target-gated duplicate global values
before name resolution, matching target-gated function behavior. Add a focused
AArch64/RISC-V IR or object regression for duplicate cfg global names.

## Resolution (2026-07-15)

Target-aware top-level global filtering is shared across native discovery,
imports, driver/JIT, interpreter, and module loading. The focused object
regressions were added but not executed in this source-only audit.
