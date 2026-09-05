# Cosmos MMU/cache pure-policy migration test plan

## Scope

This plan covers only the 22 deterministic functions from
`cosmos_cache_way_shift` through `cosmos_mmu_poll_allowed`, their narrow C
contract/oracle boundary, and production C-to-Simple object linking. CP15,
MMIO, barriers, translation-table storage, firmware boot, and board behavior
remain separate. This plan makes no whole-HAL or board-coverage claim.

## Pinned semantic decisions

The stable indices below map to the low/high true/false bitsets returned by
actual policy executions. Every outcome is required: 37 decisions, 74 outcome
bits.

| Index | Decision ID |
|---:|---|
| 0 | `cache.multiple-ways` |
| 1 | `sctlr.required-set-present` |
| 2 | `sctlr.forbidden-bits-clear` |
| 3 | `sctlr.policy-valid` |
| 4 | `control.vbar-match` |
| 5 | `control.ttbr0-match` |
| 6 | `control.dacr-domain0-client` |
| 7 | `control.sctlr-valid` |
| 8 | `control.all-registers-valid` |
| 9 | `scu.primary-cpu` |
| 10 | `cache.scu-enabled` |
| 11 | `cache.actlr-smp-enabled` |
| 12 | `l2-executable.small-page` |
| 13 | `l2-executable.xn-clear` |
| 14 | `l2-writable.small-page` |
| 15 | `l2-writable.ap-rw` |
| 16 | `l2-writable.apx-clear` |
| 17 | `l2-write-execute.executable` |
| 18 | `l2-write-execute.writable` |
| 19 | `firmware-l2.at-or-above-base` |
| 20 | `firmware-l2.at-or-below-end` |
| 21 | `firmware-l2.rx-page` |
| 22 | `device-section.nfc` |
| 23 | `device-section.pcie` |
| 24 | `device-section.cpu-private` |
| 25 | `device-section.slcr` |
| 26 | `device-section.gic-scu` |
| 27 | `l1.firmware-section` |
| 28 | `l1.ddr-at-or-above-base` |
| 29 | `l1.ddr-at-or-below-end` |
| 30 | `l1.dma-window` |
| 31 | `l1.device-section` |
| 32 | `l1.ocm-section` |
| 33 | `l1.mapped` |
| 34 | `ocm-l2.section-match` |
| 35 | `ocm-l2.at-or-above-high` |
| 36 | `mmu.poll-allowed` |

## Gates

1. Compile and execute the frozen `COSMOS_CONTRACT_TEST` C bridge without any
   Simple symbol dependency.
2. Compile production `cosmos_mmu_cache.c` for Cortex-A9 and require its exact
   18-symbol Simple import closure.
3. Require admitted Stage-4 compiler provenance before any native Simple
   evidence; missing provenance is failure, not skip or fallback.
4. Require exactly 22 C ABI exports and no undefined runtime closure in the
   host and ARM policy objects.
5. Compare all 22 Simple functions with the independent pre-migration C oracle
   over the complete 2,829-case boundary/cartesian matrix.
6. Aggregate bitsets returned by actual production evaluators and require low
   `0xFFFFFFFF/0xFFFFFFFF` plus high `0x1F/0x1F` true/false masks.
7. Relocatable-link the production Cortex-A9 C owner with the ARM Simple object
   and reject any unresolved `cosmos_mmu_cache_policy_*` symbol.
