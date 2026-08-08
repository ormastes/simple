# Cosmos+ OpenSSD Production HAL System Test Plan

## Evidence Classes

- **H0 - Static/build:** strict compilation, linking, ELF inspection, unresolved
  symbols, source contract guards. Necessary but not runtime evidence.
- **H1 - Host/QEMU:** executable pure-logic self-tests, QEMU Zynq boot,
  packager positive/rejection tests, and host mock-MMIO state machines.
- **H2 - Board:** physical Cosmos+ BootROM/FSBL, PL, NAND, PCIe, SMP/cache, reset,
  power-loss, thermal, and endurance evidence. Required for production.

## Hardware-Independent Scenarios

| ID | Scenario and pass condition | Evidence |
|---|---|---|
| ST-001 | QEMU profile builds every HAL unit with warnings as errors; output is ELF32 ARM `ET_EXEC`, nonzero entry, no unresolved symbols. | H0 |
| ST-002 | `xilinx-zynq-a9` boots and prints runtime, MMU/L1/PL310, and GIC `OK`; CPU1, FSBL, NFC, and PCIe are `UNAVAILABLE`; software PASS and silicon PENDING appear; no FAIL appears. | H1 |
| ST-003 | Silicon profile compiles separately and contains silicon PASS/FAIL identity but is never executed on the host. An unbound image must keep NFC/PCIe unavailable. | H0 |
| ST-004 | Runtime ABI runner covers copy/move/fill/string aliases, signed/unsigned division, divide-by-zero hook, and host/ARM unresolved-symbol closure. | H1 executed |
| ST-005 | Host MMIO driver validates pinned NFC offsets/commands, 8x8 topology, both LUN ranges, erase alignment, NAND status, ECC validity, DMA range/overlap, and channel quarantine. | H1 executed |
| ST-006 | Standalone PCIe runner validates upstream aperture/IDs/BAR, HWH IRQ 61 level-high binding, stable link snapshots, command FIFO/16-DW SRAM fetch, three-word completion commit, direct/AUTO host DMA FIFO ordering, link loss, and timeout. IRQ is config/link/error only. | H1 executed |
| ST-007 | Host MMIO driver covers valid FSBL handoff, fail-closed PL access, and missing `PCFG_DONE`; every physical-board predicate remains H2 work. | H1 executed |
| ST-008 | SMP/cache runner covers CPU1 vector/DSB/SEV ordering, generation ACK/cancel, GIC bounds, SCU/`ACTLR.SMP`, and cache operand contracts. | H1 executed |
| ST-009 | SMP/cache runner checks section descriptors, TTBR0 WBWA/shareability, `clz(ways-1)` set/way operands, per-core initialization, and PL310 contract markers. | H1 executed |
| ST-010 | Bounded QEMU injections execute the production prefetch/data-abort vectors and verify kind, syndrome, fault address, PC, and terminal non-resumption. | H1 executed |
| ST-011 | Packager accepts explicit valid fixtures and rejects missing/empty/aliased input, non-ELF, wrong endian/machine/type, zero entry, no `PT_LOAD`, QEMU identity, absent silicon identity, unsynchronized bitstream, malformed/truncated/empty Bootgen output, and unparseable partition metadata. Manifest hashes must match. | H1 executed |
| ST-012 | Profile note, full source closure, compiler/linker receipt, and manifest v3 bind clean revision, board identity, boot mode, contract/DMA values, Bootgen, and all artifact hashes; omission/hash mutation is rejected. | H1 executed; physical package use remains H2 |
| ST-013 | NVMe IO callback core executes empty/success/invalid/media-failure/budget/retry paths, preserves queue/slot/sequence/CID, validates SCT/SC/DNR and controller AUTO-DMA spans, and compiles for ARM. | H1 executed |
| ST-014 | PCIe bridge runner decodes DW0/DW1/DW6..DW12, validates direct PRP2 and controller-managed PRP-list edges, preserves identity, retries only before any completion write, and treats post-start failure as non-retryable. | H1 corrected host/ARM PASS |
| ST-015 | NVMe admin runner covers bounded Identify/SMART, queue lifecycle, Number-of-Queues NSID/max, Abort result bits, CQ IEN/IV, SQ QPRIO, SMART NSID/RAE, AER, publication retry/latching, and unsupported format/firmware rejection. | H1 corrected host/ARM PASS |
| ST-016 | FTL/NFC runners check PPA geometry, append-before-map ordering, dual checkpoints, replay validation, torn tails, retirement, reserve/GC, explicit media formats, journal reclamation, DMA isolation, tag validation, startup binding, and host/ARM composition. | H1 PASS |
| ST-017 | Dispatcher runner proves one destructive FIFO fetch per entry, queue-zero admin routing, nonzero IO routing, reserved-field rejection, and completion retry/terminal blocking. | H1 host/ARM PASS before final compile-only cleanup |
| ST-018 | A current pure-Simple runner executes the fourteen-scenario SSpec and generates its manual. | **Blocked:** no current runner; Stage 2/3 pass and Stage 4 clears the prior parser/HIR crashes, then fails on unresolved partial/header-only facade imports. |
| ST-019 | Focused host composition injects corrected ECC, returns intact data, relocates and rereads the page, rejects a stale PPA, preserves L2P on injected copy failure, remounts/replays the destination, and passes strict ARM compile plus relocatable link. | H1 PASS |

The host MMIO, ARM abort, and SMP/cache runners are executable H1 evidence. Static source
guards and synthetic package fixtures remain supplementary; they do not replace
physical board evidence.

## Exact Host Commands

```sh
COSMOS_BUILD_MODE=qemu sh src/os/kernel/arch/arm32/cosmos/build.shs --run
COSMOS_BUILD_MODE=silicon \
COSMOS_SILICON_PROFILE=openssd2-8ch8way-v3.0.0 \
  sh src/os/kernel/arch/arm32/cosmos/build.shs
sh test/02_integration/os/cosmos/run_cosmos_hal_mmio_test.shs
sh test/02_integration/os/cosmos/run_cosmos_pcie_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_firmware_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_pcie_adapter_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_admin_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_nfc_backend_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_ftl_physical_composition_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_ecc_refresh_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ecc_refresh_build_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_storage_link_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_smp_cache_contract_test.shs
readelf -hW build/os/simpleos_cosmos_openssd_silicon.elf
test -z "$(nm -u build/os/simpleos_cosmos_openssd_silicon.elf)"
sh src/os/kernel/arch/arm32/cosmos/package_boot.shs --self-test
bin/release/simple test \
  test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl \
  --mode=interpreter
```

`bin/release/simple` must be current before the SSpec is run. A stale binary
with the obsolete `rt_env_set` ABI is not evidence. Host/ARM composition proves
software binding only; physical NVMe IO and board acceptance remain pending.

## Board Scenarios

| ID | Scenario and pass condition | Evidence |
|---|---|---|
| BT-001 | BootROM loads the exact FSBL, verified upstream-compatible bitstream, and bound silicon ELF from the selected boot device; hashes match the package manifest and serial reaches silicon PASS without abort. | REQ-001, REQ-008..012 |
| BT-002 | Every channel/way performs reset, erase, program, read, status, deterministic/random data comparison, and ECC-margin checks on reserved destructive-test blocks. | REQ-002, REQ-003 |
| BT-003 | Controlled power interruption at erase/program/journal/flush boundaries recovers without silent acknowledged-data loss or use of quarantined media. | REQ-003, NFR-004, NFR-011 |
| BT-004 | Linux host enumerates `10ee:7028`, NVMe class `010802`, 8 KiB BAR0, Bus Master and MSI; admin and IO queues complete; DMA data compares; reset/PERST/link recovery succeed. | REQ-004 |
| BT-005 | CPU1 release/ACK, SGI/PPI/SPI delivery, shared-memory ping-pong, cache-line ownership, DMA visibility, and concurrent NAND/PCIe load complete with no stale data or lost interrupt. | REQ-006, REQ-007 |
| BT-006 | Cold boot, warm reset, sustained mixed IO, and thermal/endurance campaign complete for the predeclared duration/counts with zero silent corruption and retained telemetry. | REQ-012, NFR-011 |

Detailed execution and evidence retention are in
`doc/07_guide/hardware/cosmos_openssd_production_firmware.md`.
The retained campaign is accepted only by
`scripts/check/check-nvme-firmware-remaining-gates.shs --board-evidence DIR`.
Each BT row must bind one nonempty in-campaign raw log by SHA-256 and name the
independent reviewer recorded in `manifest.txt`; the gate also verifies the
source/board/boot-mode/artifact binding through `boot.bin.manifest`.

## Traceability

| Requirement | Host scenarios | Board scenarios |
|---|---|---|
| REQ-001 | ST-002, ST-003, ST-012 | BT-001 |
| REQ-002 | ST-005 | BT-002 |
| REQ-003 | ST-005, ST-016, ST-019 | BT-002, BT-003 |
| REQ-004 | ST-006, ST-013..ST-017 | BT-004 |
| REQ-005 | ST-001, ST-004 | BT-001 |
| REQ-006 | ST-008 | BT-005 |
| REQ-007 | ST-009 | BT-005 |
| REQ-008 | ST-007, ST-010 | BT-001 |
| REQ-009 | ST-002, ST-003, ST-010 | BT-001 |
| REQ-010 | ST-011, ST-012 | BT-001 |
| REQ-011 | ST-001..ST-019 | N/A |
| REQ-012 | N/A | BT-001..BT-006 |
| NFR-001 | ST-005..ST-019 | BT-002, BT-004, BT-005 |
| NFR-002 | ST-002, ST-003, ST-007, ST-012 | BT-001 |
| NFR-003 | ST-010 | BT-001 |
| NFR-004 | ST-005, ST-006, ST-013, ST-014, ST-016, ST-019 | BT-002..BT-004 |
| NFR-005 | ST-008, ST-009 | BT-005 |
| NFR-006 | ST-001, ST-004 | BT-001 |
| NFR-007 | ST-001, ST-011, ST-012 | BT-001 |
| NFR-008 | ST-011 | BT-001..BT-006 |
| NFR-009 | ST-002, ST-003 | BT-001 |
| NFR-010 | This matrix, ST-018 after execution | BT-001..BT-006 |
| NFR-011 | N/A | BT-003, BT-006 |
| NFR-012 | ST-001..ST-019 | BT-001..BT-006 |

## Current Evidence, 2026-07-27

Scoped H0/H1 runners pass through persistent FTL/NFC composition, UART startup,
dispatcher routing, ECC refresh relocation, and strict ARM linkage. External
software package provenance in `ST-012` passes. `ST-018` is blocked because no current
pure-Simple runner exists. The unchanged-tree strict bootstrap rebuilt Rust
authority and passed Stage 2/3 sanity. Stage 2 was
`00fcb65729acfe1f7bd30e113d7d96bea4cd7ff2e4f596667cda8c6a97c89411`;
Stage 3 was
`772f9a2e6d104500c5cd1c661c15b6e0083fd9c936787803bb05f5ad824c17b3`.
Stage 4 cleared the prior parser/HIR crashes, then failed on unresolved names
from partial/header-only import facades at 5,492,252 KiB peak RSS.
Official Bootgen v2026.1, the pinned bitstream, vendor-generated FSBL, and real
package have retained hashes. Manifest v3 and its standalone verifier pass on
synthetic fixtures; final SSpec/doc generation and all `BT-*`
evidence remain pending. Production is **BLOCKED/FAIL**;
REQ-012/NFR-011 remain excluded from passing executable `@req` declarations.
