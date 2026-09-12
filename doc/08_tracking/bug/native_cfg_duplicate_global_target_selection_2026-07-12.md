# Native cfg duplicate global target selection

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Status (2026-07-15 -> CLOSED-STALE 2026-09-12):** source implemented; focused AArch64/RISC-V object
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

## Triage 2026-09-12
The 2026-07-15 status already noted regression execution remains pending; still unexecuted 2 months later. Older than 45 days with no cheap repro re-run; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
