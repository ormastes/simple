# nvme_cosmos_openssd_boot_spec

> Executes the host runtime ABI, MMIO, ARM abort, PCIe transport, FTL metadata, NVMe IO/admin callback-service, and SMP/cache integration drivers, boots the unbound QEMU image, builds the exact `openssd2-8ch8way-v3.0.0` silicon profile, inspects its ELF identity, runs packaging rejection checks, and guards the freestanding ARM ABI edges. The NVMe runners are host/ARM contract tests. The PCIe bridge decodes the controller transport but requires caller-provided media callbacks. The service objects, crash-consistent FTL metadata, physical NFC persistence backend, 4 KiB-to-16 KiB media adapter, and fail-closed UART foreground startup compile for the pinned silicon profile. Physical-board proof remains pending. Corrected bridge/admin runners cover Abort bits, Number of Queues NSID/max, CQ IEN/IV, SQ QPRIO, SMART NSID/RAE, PCIe zero-write retry boundaries, non-retryable post-start completion behavior, and PRP edges.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 14 | 14 | 0 | 0 |

## Scope

The executable spec runs the Cosmos host runtime ABI, MMIO, ARM abort, PCIe
transport, FTL metadata, NVMe IO/admin callback-service, and SMP/cache integration drivers, boots the
unbound QEMU image, builds and inspects the exact bound silicon profile, runs
the boot package self-test, and checks ARM EABI edge coverage.
All NVMe runners are host/ARM contract tests. The bridge decodes the real
controller transport but requires mandatory caller-supplied media callbacks.
The service objects, crash-consistent FTL metadata, physical NFC persistence
backend, 4 KiB-to-16 KiB media adapter, and fail-closed UART foreground startup
compile for the pinned silicon profile. Physical-board proof remains pending.

Executes the host runtime ABI, MMIO, ARM abort, PCIe transport, FTL metadata, NVMe IO/admin callback-service, and SMP/cache integration drivers, boots the unbound QEMU image, builds the exact `openssd2-8ch8way-v3.0.0` silicon profile, inspects its ELF identity, runs packaging rejection checks, and guards the freestanding ARM ABI edges. The NVMe runners are host/ARM contract tests. The PCIe bridge decodes the controller transport but requires caller-provided media callbacks. The service objects, crash-consistent FTL metadata, physical NFC persistence backend, 4 KiB-to-16 KiB media adapter, and fail-closed UART foreground startup compile for the pinned silicon profile. Physical-board proof remains pending. Corrected bridge/admin runners cover Abort bits, Number of Queues NSID/max, CQ IEN/IV, SQ QPRIO, SMART NSID/RAE, PCIe zero-write retry boundaries, non-retryable post-start completion behavior, and PRP edges.

Run only with a current pure-Simple bootstrap runner:

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/cosmos_openssd_production_hal.md |
| Plan | doc/03_plan/sys_test/cosmos_openssd_production_hal.md |
| Design | doc/05_design/cosmos_openssd_production_hal.md |
| Source | `test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Executes the host runtime ABI, MMIO, ARM abort, PCIe transport, FTL metadata,
NVMe IO/admin callback-service, and SMP/cache integration drivers, boots the unbound QEMU image, builds
the exact `openssd2-8ch8way-v3.0.0` silicon profile, inspects its ELF identity,
runs packaging rejection checks, and guards the freestanding ARM ABI edges.
The NVMe runners are host/ARM contract tests. The PCIe bridge decodes the
controller transport but requires caller-provided media callbacks. The service
objects, crash-consistent FTL metadata, physical NFC persistence backend,
4 KiB-to-16 KiB media adapter, and fail-closed UART foreground startup compile
for the pinned silicon profile. Physical-board proof remains pending.
Corrected bridge/admin runners cover Abort bits, Number of Queues NSID/max,
CQ IEN/IV, SQ QPRIO, SMART NSID/RAE, PCIe zero-write retry boundaries,
non-retryable post-start completion behavior, and PRP edges.

## Syntax

Run only with `bin/simple` rebuilt and deployed from the current tree in
interpreter mode. A stale release runner with the obsolete `rt_env_set` ABI can
crash before any scenario executes and is not evidence. Do NOT invoke
`bin/release/simple`: that path is a production-guard wrapper which refuses to
exec a non-production runtime ("refusing non-production Simple runtime") and
exits without running anything, which reads as a firmware-shaped false RED.

## Examples

`bin/simple test test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl --mode=interpreter`

Source SHA-256: `787b546a04b4bfa1a02b940c9fce2ddcc801c5136bd42e119ae055c6ef781d54`.
<!-- sspec-maintain:provenance:end -->

Passing proves hardware-independent host and QEMU behavior, exact silicon
profile compilation, ELF identity, and package validation. It does not prove
physical NAND IO/ECC, PCIe enumeration/MSI/DMA/reset, CPU1 coherency, BootROM
boot, power-loss recovery, thermal behavior, or endurance. The board-only
requirements REQ-012 and NFR-011 are excluded from `@req` and remain pending
until retained evidence from the identified board satisfies the production
guide. The NVMe callback-service scenario does not bind real PCIe/NFC adapters
and is not board evidence. The current strict bootstrap reached Stage 3, but
its third/final Stage 4 attempt was terminated at about 64 GiB RSS; no current
deployed `bin/simple` exists and this spec has not been executed or doc-generated.

## Scenarios

### 1. Host FSBL, NFC, and PCIe MMIO

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_hal_mmio_test.shs
```

Requires all six case markers and the terminal marker
`STATUS: PASS cosmos host mock-MMIO integration`, with exit `0` and no `FAIL`.
The driver exercises valid and fail-closed FSBL handoff, bounded NFC setup,
NFC read/program/erase/ECC, timeout quarantine, and PCIe
link/function/MSI/admin state.

### 2. Standalone PCIe contract

- should execute the standalone PCIe contract runner
- Compile and run the bounded PCIe controller contract driver
   - Expected: code equals `0`
   - Expected: auto_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the standalone PCIe contract runner")
step("Compile and run the bounded PCIe controller contract driver")
val (out, err, code) = _run("sh " + HOST_PCIE)
expect(code).to_equal(0)
expect(out).to_contain("cosmos PCIe contract: PASS")
_expect_no_fail(out, err, "Cosmos PCIe contract")
val (auto_out, auto_err, auto_code) = _run(
    "sh " + HOST_PCIE_AUTO_COMPLETION
)
expect(auto_code).to_equal(0)
expect(auto_out).to_contain(
    "cosmos PCIe AUTO completion contract: PASS"
)
expect(auto_out).to_contain(
    "cosmos PCIe AUTO completion ARM compile: PASS"
)
_expect_no_fail(auto_out, auto_err, "Cosmos PCIe AUTO completion")
```

Requires exit `0`, no `FAIL`, and `cosmos PCIe contract: PASS`. It validates
HWH-bound IRQ `61` as level-high, stable endpoint snapshots, command FIFO plus
16-DW SRAM fetch, two-word AUTO completion with captured-slot release, and
direct/AUTO host-DMA FIFO ordering. CPU0 targeting is a local policy; IRQ `61` is only for
configuration/link/error state, not command arrival. Board IRQ delivery, DMA
data integrity, enumeration, reset, and recovery remain pending.

### 3. ARM prefetch/data abort contract

- should execute actual ARM prefetch and data abort entry paths
- Run bounded QEMU injections through the production ARM vectors
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute actual ARM prefetch and data abort entry paths")
step("Run bounded QEMU injections through the production ARM vectors")
val (out, err, code) = _run("sh " + HOST_ABORT)
expect(code).to_equal(0)
expect(out).to_contain("prefetch: PASS")
expect(out).to_contain("data: PASS")
expect(out).to_contain("cosmos ARM prefetch/data abort contract: PASS")
_expect_no_fail(out, err, "Cosmos ARM abort contract")
```

Requires bounded QEMU execution, `prefetch: PASS`, `data: PASS`, and
`cosmos ARM prefetch/data abort contract: PASS`. It enters through the
production ARM vectors, checks captured syndrome/address/PC, and proves that
neither exception resumes. Physical-board abort behavior remains pending.

### 4. NVMe IO callback service contract

- should execute the hardened NVMe IO callback service contract runner
- Run bounded IO validation, identity, DMA-span, and publication tests
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the hardened NVMe IO callback service contract runner")
step("Run bounded IO validation, identity, DMA-span, and publication tests")
val (out, err, code) = _run("sh " + HOST_NVME)
expect(code).to_equal(0)
expect(out).to_contain("cosmos NVMe firmware contract: PASS")
expect(out).to_contain("cosmos NVMe firmware ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe callback service contract")
```

Requires exit `0`, no `FAIL`, `cosmos NVMe firmware contract: PASS`, and
`cosmos NVMe firmware ARM compile: PASS`. It covers bounded queue polling,
queue/slot/sequence/CID identity, SCT/SC/DNR completion status, exact
contiguous DMA span validation, distinct read/write media failures, basic Write
Zeroes, DSM Deallocate callback semantics, and retry only
before a provably uncommitted completion. The separate FTL scenario tests only
the metadata core.

### 5. FTL metadata contract

- should execute the crash-consistent FTL metadata contract runner
- Run PPA, journal, checkpoint, recovery, retirement, and fail-closed checks
   - Expected: code equals `0`
   - Expected: gc_code equals `0`
   - Expected: discard_code equals `0`
   - Expected: journal_code equals `0`
   - Expected: trim_code equals `0`
   - Expected: tx_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the crash-consistent FTL metadata contract runner")
step("Run PPA, journal, checkpoint, recovery, retirement, and fail-closed checks")
val (out, err, code) = _run("sh " + HOST_FTL)
expect(code).to_equal(0)
expect(out).to_contain("cosmos FTL contract: PASS")
expect(out).to_contain("cosmos FTL ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos FTL metadata contract")
val (gc_out, gc_err, gc_code) = _run("sh " + HOST_FTL_GC)
expect(gc_code).to_equal(0)
expect(gc_out).to_contain("cosmos FTL GC contract: PASS")
expect(gc_out).to_contain("cosmos FTL GC ARM compile: PASS")
_expect_no_fail(gc_out, gc_err, "Cosmos FTL GC contract")
val (discard_out, discard_err, discard_code) = _run(
    "sh " + HOST_FTL_DISCARD
)
expect(discard_code).to_equal(0)
expect(discard_out).to_contain("cosmos FTL discard contract: PASS")
expect(discard_out).to_contain(
    "cosmos FTL discard ARM compile: PASS"
)
_expect_no_fail(discard_out, discard_err, "Cosmos FTL discard")
val (journal_out, journal_err, journal_code) = _run(
    "sh " + HOST_FTL_JOURNAL
)
expect(journal_code).to_equal(0)
expect(journal_out).to_contain(
    "cosmos FTL journal reclaim contract: PASS"
)
expect(journal_out).to_contain(
    "cosmos FTL journal reclaim ARM compile: PASS"
)
_expect_no_fail(journal_out, journal_err, "Cosmos FTL journal reclaim")
val (trim_out, trim_err, trim_code) = _run(
    "sh " + HOST_FTL_RECOVERY_TRIM
)
expect(trim_code).to_equal(0)
expect(trim_out).to_contain(
    "cosmos FTL recovery trim contract: PASS"
)
expect(trim_out).to_contain(
    "cosmos FTL recovery trim ARM compile: PASS"
)
_expect_no_fail(trim_out, trim_err, "Cosmos FTL recovery trim")
val (tx_out, tx_err, tx_code) = _run(
    "sh " + HOST_FTL_TRANSACTION
)
expect(tx_code).to_equal(0)
expect(tx_out).to_contain(
    "cosmos FTL transaction recovery contract: PASS"
)
expect(tx_out).to_contain(
    "cosmos FTL transaction recovery ARM compile: PASS"
)
_expect_no_fail(tx_out, tx_err, "Cosmos FTL transaction recovery")
```

Requires all FTL host/ARM PASS pairs. It covers PPA geometry, journal ordering,
dual-checkpoint recovery, torn-tail handling, retirement guards,
fail-sticky ambiguous writes, 10% capacity reserve, bounded relocation, and
erase-after-move ordering. Additional focused checks cover durable discard,
64-bit journal reclamation, checkpoint trim-state reconstruction, whole-
transaction journal reservation, torn physical holes, and trailing allocation
recovery.

### 6. Persistent NFC media and startup composition

- should bind persistent NFC media and fail closed outside silicon
- Run NFC wire-format, media staging, and startup composition checks
   - Expected: nfc_code equals `0`
   - Expected: nfc_io_code equals `0`
   - Expected: nfc_dma_code equals `0`
   - Expected: media_code equals `0`
   - Expected: physical_code equals `0`
   - Expected: tag_code equals `0`
   - Expected: refresh_code equals `0`
   - Expected: refresh_build_code equals `0`
   - Expected: startup_code equals `0`
   - Expected: link_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 117 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind persistent NFC media and fail closed outside silicon")
step("Run NFC wire-format, media staging, and startup composition checks")
val (nfc_out, nfc_err, nfc_code) = _run("sh " + HOST_FTL_NFC)
expect(nfc_code).to_equal(0)
expect(nfc_out).to_contain(
    "cosmos FTL NFC persistence backend: PASS"
)
expect(nfc_out).to_contain(
    "cosmos FTL NFC persistence backend ARM compile: PASS"
)
_expect_no_fail(nfc_out, nfc_err, "Cosmos FTL NFC persistence")
val (nfc_io_out, nfc_io_err, nfc_io_code) = _run(
    "sh " + HOST_FTL_NFC_IO
)
expect(nfc_io_code).to_equal(0)
expect(nfc_io_out).to_contain(
    "cosmos FTL NFC IO fail-closed: PASS"
)
expect(nfc_io_out).to_contain(
    "cosmos FTL NFC IO fail-closed ARM compile: PASS"
)
_expect_no_fail(nfc_io_out, nfc_io_err, "Cosmos FTL NFC IO")
val (nfc_dma_out, nfc_dma_err, nfc_dma_code) = _run(
    "sh " + HOST_FTL_NFC_DMA
)
expect(nfc_dma_code).to_equal(0)
expect(nfc_dma_out).to_contain(
    "cosmos FTL NFC metadata/payload DMA isolation: PASS"
)
expect(nfc_dma_out).to_contain(
    "cosmos FTL NFC metadata/payload DMA isolation ARM compile: PASS"
)
_expect_no_fail(nfc_dma_out, nfc_dma_err, "Cosmos FTL NFC DMA")

val (media_out, media_err, media_code) = _run(
    "sh " + HOST_FTL_MEDIA
)
expect(media_code).to_equal(0)
expect(media_out).to_contain(
    "cosmos NVMe FTL media adapter: PASS"
)
expect(media_out).to_contain(
    "cosmos NVMe FTL media adapter ARM compile: PASS"
)
_expect_no_fail(media_out, media_err, "Cosmos NVMe FTL media")

val (physical_out, physical_err, physical_code) = _run(
    "sh " + HOST_FTL_PHYSICAL
)
expect(physical_code).to_equal(0)
expect(physical_out).to_contain(
    "cosmos NVMe physical media composition: PASS"
)
expect(physical_out).to_contain(
    "cosmos NVMe physical media composition ARM compile: PASS"
)
_expect_no_fail(
    physical_out, physical_err, "Cosmos NVMe physical composition"
)

val (tag_out, tag_err, tag_code) = _run("sh " + HOST_FTL_TAG)
expect(tag_code).to_equal(0)
expect(tag_out).to_contain(
    "cosmos NVMe media page-tag validation: PASS"
)
expect(tag_out).to_contain(
    "cosmos NVMe media page-tag validation ARM compile: PASS"
)
_expect_no_fail(tag_out, tag_err, "Cosmos NVMe page tag")

val (refresh_out, refresh_err, refresh_code) = _run(
    "sh " + HOST_FTL_ECC_REFRESH
)
expect(refresh_code).to_equal(0)
expect(refresh_out).to_contain(
    "cosmos NVMe ECC refresh relocation: PASS"
)
expect(refresh_out).to_contain(
    "cosmos NVMe ECC refresh relocation ARM compile: PASS"
)
_expect_no_fail(refresh_out, refresh_err, "Cosmos NVMe ECC refresh")

val (refresh_build_out, refresh_build_err, refresh_build_code) = _run(
    "sh " + HOST_FTL_ECC_BUILD
)
expect(refresh_build_code).to_equal(0)
expect(refresh_build_out).to_contain(
    "cosmos ECC refresh API and ARM relocatable link: PASS"
)
_expect_no_fail(
    refresh_build_out, refresh_build_err, "Cosmos ECC refresh build"
)

val (startup_out, startup_err, startup_code) = _run(
    "sh " + HOST_STORAGE_STARTUP
)
expect(startup_code).to_equal(0)
expect(startup_out).to_contain(
    "cosmos storage QEMU fail-closed startup: PASS"
)
expect(startup_out).to_contain(
    "cosmos storage startup ARM profiles compile: PASS"
)
_expect_no_fail(startup_out, startup_err, "Cosmos storage startup")

val (link_out, link_err, link_code) = _run(
    "sh " + HOST_STORAGE_LINK
)
expect(link_code).to_equal(0)
expect(link_out).to_contain(
    "cosmos storage qemu production link: PASS"
)
expect(link_out).to_contain(
    "cosmos storage silicon production link: PASS"
)
_expect_no_fail(link_out, link_err, "Cosmos storage production link")
```

Requires all host/ARM PASS pairs. It covers explicit little-endian metadata,
program-once page tags, checkpoint/journal persistence and reclamation,
4 KiB NVMe staging across 16 KiB NAND pages, LR retry policy, DSM discard, and
QEMU fail-closed startup. Corrected-ECC reads relocate the current page through
the FTL transaction path after host DMA completes; the old mapping remains
authoritative if relocation fails. The focused runner rereads the relocated
data, rejects a stale source PPA, injects a failed copy, and remounts/replays
the surviving mapping. Silicon mounts and recovers existing metadata only; it
never formats NAND automatically. Physical NAND correction, PCIe DMA data
integrity, power-loss behavior, and endurance remain board-evidence
requirements.

### 7. PCIe-to-NVMe adapter contract

- should execute the PCIe-to-NVMe bridge contract runner
- Run DW0/DW1/DW6-DW12, AUTO-DMA PRP, and completion transport checks
   - Expected: code equals `0`
   - Expected: prp_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the PCIe-to-NVMe bridge contract runner")
step("Run DW0/DW1/DW6-DW12, AUTO-DMA PRP, and completion transport checks")
val (out, err, code) = _run("sh " + HOST_NVME_ADAPTER)
expect(code).to_equal(0)
expect(out).to_contain("cosmos NVMe PCIe adapter contract: PASS")
expect(out).to_contain("cosmos NVMe PCIe adapter ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe PCIe adapter contract")
val (prp_out, prp_err, prp_code) = _run(
    "sh " + HOST_NVME_PRP_CONTROL
)
expect(prp_code).to_equal(0)
expect(prp_out).to_contain("cosmos NVMe PRP/control contract: PASS")
expect(prp_out).to_contain("cosmos NVMe FUA/LR contract: PASS")
expect(prp_out).to_contain(
    "cosmos NVMe PRP/control ARM compile: PASS"
)
_expect_no_fail(prp_out, prp_err, "Cosmos NVMe PRP/control")
```

Requires `cosmos NVMe PCIe adapter contract: PASS` and
`cosmos NVMe PCIe adapter ARM compile: PASS`. It decodes DW0, DW1, and
DW6..DW12, preserves command identity, accepts direct PRP2 and controller-
managed PRP-list pointers,
maps controller completion publication into the IO core, checks PRP boundaries,
decodes Write Zeroes and DSM Deallocate, forwards LR, enforces FUA through
flush-before-completion, retries only before any completion write, and treats
post-start completion failure as non-retryable. The pinned controller's AUTO
DMA hardware walks PRP lists; firmware does not duplicate that parser. Media
callbacks are mandatory, so this is not yet physical data-path evidence.

### 8. NVMe admin callback core

- should execute the NVMe admin callback core contract runner
- Run corrected bounded Identify, SMART, queue, feature, Abort, and AER checks
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the NVMe admin callback core contract runner")
step("Run corrected bounded Identify, SMART, queue, feature, Abort, and AER checks")
val (out, err, code) = _run("sh " + HOST_NVME_ADMIN)
expect(code).to_equal(0)
expect(out).to_contain("cosmos NVMe admin contract: PASS")
expect(out).to_contain("cosmos NVMe admin ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe admin contract")
```

Requires `cosmos NVMe admin contract: PASS` and
`cosmos NVMe admin ARM compile: PASS`. It covers bounded Identify,
SMART, queue lifecycle, Number-of-Queues features, Abort, AER, retry/latching,
and explicit Invalid Opcode for unsupported format and firmware commands. Edge
coverage includes Abort result bits, global NSID and maximum queue negotiation,
CQ IEN/IV, SQ QPRIO, and SMART NSID/RAE. It has no PCIe/PRP or persistent
media binding.

### 9. Single-owner NVMe dispatcher

- should route the single PCIe command FIFO to admin or IO exactly once
- Run queue-zero admin, IO, retry, terminal, and reserved-field routing checks
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route the single PCIe command FIFO to admin or IO exactly once")
step("Run queue-zero admin, IO, retry, terminal, and reserved-field routing checks")
val (out, err, code) = _run("sh " + HOST_NVME_DISPATCH)
expect(code).to_equal(0)
expect(out).to_contain("cosmos NVMe dispatcher contract: PASS")
expect(out).to_contain("cosmos NVMe dispatcher ARM compile: PASS")
_expect_no_fail(out, err, "Cosmos NVMe dispatcher contract")
```

Requires the dispatcher host/ARM PASS pair. It fetches each controller FIFO
entry once, routes queue zero to admin and nonzero queues to IO, and prevents a
pending or terminal completion from consuming another command. Physical queue
register programming remains board-evidence work; UART foreground startup is
source-bound and ARM-compiled.

### 10. Host SMP, GIC, MMU, and cache

- should execute the host SMP, GIC, MMU, and cache contracts
- Compile and run the host SMP/cache contract driver
   - Expected: code equals `0`
- Verify cache operands, coherency ordering, GIC limits, and CPU1 protocol


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the host SMP, GIC, MMU, and cache contracts")
step("Compile and run the host SMP/cache contract driver")
val (out, err, code) = _run("sh " + HOST_SMP_CACHE)
expect(code).to_equal(0)

step("Verify cache operands, coherency ordering, GIC limits, and CPU1 protocol")
expect(out).to_contain("STATUS: PASS cosmos SMP/cache contract")
_expect_no_fail(out, err, "Cosmos host SMP/cache contract")
```

Requires exit `0`, no `FAIL`, and
`STATUS: PASS cosmos SMP/cache contract`. The driver checks cache set/way and
TTBR0 operands, SCU/ACTLR coherency ordering, GIC bounds, and the generation
tagged CPU1 release/ACK protocol.

The SMP/GIC policy owner is
`src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic_policy.spl`; its C ABI is
`src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic_policy.h`, and its focused gate
is `scripts/check/check-cosmos-smp-gic-policy.shs`. That gate requires exact
C-oracle versus Simple parity for 234 rows, execution of all 17 named policy
decisions and all 34 outcomes, and atomic evidence publication bound to an
admitted Stage-4 binary and its adjacent provenance. These scoped software
counts are not whole-HAL or physical-board coverage.

### 11. Unbound QEMU boot

- should boot the unbound QEMU image with an exact software-only verdict
- Build every Cosmos HAL unit and boot the Zynq QEMU machine
   - Expected: code equals `0`
- Verify the hardware-independent runtime, MMU/cache, and GIC statuses
- Verify every board-only lane remains explicitly unavailable
- Keep physical production acceptance pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should boot the unbound QEMU image with an exact software-only verdict")
step("Build every Cosmos HAL unit and boot the Zynq QEMU machine")
val (out, err, code) = _run("COSMOS_BUILD_MODE=qemu sh " + BUILD + " --run")
expect(code).to_equal(0)
expect(out).to_contain(
    "built build/os/simpleos_cosmos_openssd.elf (clean, unbound, entry="
)
expect(out).to_contain("COSMOS+ OpenSSD (Zynq-7000 / Cortex-A9) boot OK")

step("Verify the hardware-independent runtime, MMU/cache, and GIC statuses")
expect(out).to_contain("[cosmos] ARMv7 runtime: OK")
expect(out).to_contain("[cosmos] MMU/L1/PL310: OK")
expect(out).to_contain("[cosmos] GIC primary: OK")

step("Verify every board-only lane remains explicitly unavailable")
expect(out).to_contain("[cosmos] CPU1 release: UNAVAILABLE")
expect(out).to_contain("[cosmos] FSBL handoff: UNAVAILABLE")
expect(out).to_contain("[cosmos] NFC PL: UNAVAILABLE")
expect(out).to_contain("[cosmos] PCIe PL: UNAVAILABLE")

step("Keep physical production acceptance pending")
expect(out).to_contain("COSMOS SOFTWARE HAL CHECKS PASS")
expect(out).to_contain("COSMOS SILICON VALIDATION PENDING")
_expect_absent(out, "COSMOS SILICON HAL CHECKS PASS", "Cosmos QEMU profile")
_expect_no_fail(out, err, "Cosmos QEMU profile")
```

</details>

#### should build and identify the exact bound silicon profile

- should build and identify the exact bound silicon profile
- Build the silicon image with the exact reviewed profile selector
   - Expected: code equals `0`
- Inspect ELF type, loadability, profile note, exact symbol, and link closure
   - Expected: elf_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build and identify the exact bound silicon profile")
step("Build the silicon image with the exact reviewed profile selector")
val command = "COSMOS_BUILD_MODE=silicon COSMOS_SILICON_PROFILE=" + PROFILE +
    " sh " + BUILD
val (out, err, code) = _run(command)
expect(code).to_equal(0)
expect(out).to_contain(
    "built " + SILICON_ELF + " (clean, profile=" + PROFILE + ", entry="
)
_expect_no_fail(out, err, "Cosmos bound silicon build")

step("Inspect ELF type, loadability, profile note, exact symbol, and link closure")
val inspect = "readelf -hW " + SILICON_ELF +
    " && readelf -lW " + SILICON_ELF +
    " && readelf -SW " + SILICON_ELF +
    " && readelf -sW " + SILICON_ELF +
    " && readelf -p .note.cosmos.profile " + SILICON_ELF +
    " && test -z \"$(nm -u " + SILICON_ELF + ")\""
val (elf_out, elf_err, elf_code) = _run(inspect)
expect(elf_code).to_equal(0)
expect(elf_out).to_contain("ELF32")
expect(elf_out).to_contain("EXEC")
expect(elf_out).to_contain("ARM")
expect(elf_out).to_contain("LOAD")
expect(elf_out).to_contain(".note.cosmos.profile")
expect(elf_out).to_contain(PROFILE_SYMBOL)
expect(elf_out).to_contain("profile=cosmos-plus-" + PROFILE)
expect(elf_out).to_contain("source=78601486bb5581e40628ec7e841dea8e97eff034")
expect(elf_out).to_contain("bitstream=66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2")
_expect_no_fail(elf_out, elf_err, "Cosmos silicon ELF inspection")
```

`COSMOS SILICON HAL CHECKS PASS` and every `FAIL` marker are forbidden.

Boot admission and terminal-status policy are owned by
`src/os/kernel/arch/arm32/cosmos/cosmos_boot_policy.spl` through
`cosmos_boot_policy.h`; `cosmos_uart.c` remains the MMIO/assembly/ABI bridge.
The focused `scripts/check/check-cosmos-boot-policy.shs` gate freezes 279
independent C-versus-Simple parity rows, 38 named decisions/76 outcomes, and
the independent C oracle's exact 68/68 LLVM branch outcomes. Its acceptance
receipt requires an admitted Stage-4 binary with adjacent provenance and does
not establish physical-board boot behavior.

### 12. Exact bound silicon artifact

- should reject invalid boot inputs and publish bound package metadata
- Run ELF, bitstream, alias, Bootgen metadata, hash, and manifest checks
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject invalid boot inputs and publish bound package metadata")
step("Run ELF, bitstream, alias, Bootgen metadata, hash, and manifest checks")
val (out, err, code) = _run("sh " + PACKAGE + " --self-test")
expect(code).to_equal(0)
expect(out).to_contain("COSMOS_PACKAGE_PROVENANCE_PASS source=clean board=bound tools=clang,lld,bootgen")
expect(out).to_contain("STATUS: PASS cosmos-package-boot self-test")
_expect_no_fail(out, err, "Cosmos package self-test")
```

</details>

#### should retain ARM EABI division edges and runtime self-test markers

- should retain ARM EABI division edges and runtime self-test markers
- Run host behavior and unresolved-symbol checks for the ARM runtime ABI
   - Expected: code equals `0`
- Inspect the freestanding runtime ABI and divide-by-zero hook
- Bind those edge checks to the boot-time runtime verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain ARM EABI division edges and runtime self-test markers")
step("Run host behavior and unresolved-symbol checks for the ARM runtime ABI")
val (out, err, code) = _run("sh " + HOST_RUNTIME)
expect(code).to_equal(0)
expect(out).to_contain("cosmos runtime contract: PASS")
expect(out).to_contain("cosmos runtime host/ARM ABI objects: PASS")
_expect_no_fail(out, err, "Cosmos runtime ABI contract")

step("Inspect the freestanding runtime ABI and divide-by-zero hook")
val runtime = file_read_text("src/os/kernel/arch/arm32/cosmos/cosmos_runtime.c")
expect(runtime).to_contain("__attribute__((weak)) int __aeabi_idiv0")
expect(runtime).to_contain("result = __aeabi_uidivmod(unsigned_max, unsigned_max);")
expect(runtime).to_contain("__aeabi_uidiv(unsigned_max, 2U) != 0x7FFFFFFFU")
expect(runtime).to_contain("__aeabi_idiv(signed_min, -1) != signed_min")
expect(runtime).to_contain("cosmos_udivmod(1U, 0U, &quotient, &remainder) != 0")
expect(runtime).to_contain("__aeabi_idiv0(123) != 123")
expect(runtime).to_contain("(cosmos_u64)remainder << 32")

step("Bind those edge checks to the boot-time runtime verdict")
val boot = file_read_text("src/os/kernel/arch/arm32/cosmos/cosmos_uart.c")
expect(boot).to_contain("runtime_status = cosmos_runtime_selftest();")
expect(boot).to_contain("cosmos_report_status(\"ARMv7 runtime\", runtime_status);")
expect(boot).to_contain("runtime_status == COSMOS_OK")
```

The note must bind the pinned upstream source commit and bitstream SHA-256:

```text
source=78601486bb5581e40628ec7e841dea8e97eff034
bitstream=66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2
```

### 13. Boot package validation

Runs:

```sh
sh src/os/kernel/arch/arm32/cosmos/package_boot.shs --self-test
```

Requires exit `0`, no `FAIL`,
`COSMOS_PACKAGE_PROVENANCE_PASS source=clean board=bound tools=clang,lld,bootgen`,
and `STATUS: PASS cosmos-package-boot self-test`. The wrapper owns malformed
ELF, profile, bitstream, alias, Bootgen metadata, complete compiled-source
closure, clean revision, board/boot identity, tool identity, hash, missing-key,
and manifest-mutation rejection coverage.

### 14. ARM runtime ABI edges

The runtime runner executes memory/string aliases, division edges, and host/ARM
unresolved-symbol checks. The spec also checks that `cosmos_runtime.c` retains the weak `__aeabi_idiv0` hook,
unsigned and signed extrema, signed overflow convention, quotient/remainder
packing, divide-by-zero behavior, and 64-bit remainder packing. It also checks
that `cosmos_uart.c` executes `cosmos_runtime_selftest()` and reports the
`ARMv7 runtime` status used by the QEMU scenario.

<!-- sspec-maintain:traceability:start -->
## Traceability

Passing proves software behavior only. It does not prove physical NAND IO/ECC,
PCIe enumeration/MSI/DMA/reset, CPU1 coherency, BootROM/FSBL boot, power-loss
recovery, thermal behavior, or endurance. The board-only requirements
`REQ-012` and `NFR-011` are intentionally excluded from executable `@req`
traceability and remain pending until retained evidence from the identified
Cosmos+ board satisfies the production guide. Neither host, QEMU, compile,
synthetic Bootgen, source-check success, nor the host/ARM NVMe callback
contract runner can satisfy them.

- `REQ-SSPEC-SYSTEM`
- `REQ-012`
- `REQ-SSPEC-SYSTEM;`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `899e208b4e231417bf8168413ebc75de7aa8e2b1fd944b7456209b6bcea153c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `899e208b4e231417bf8168413ebc75de7aa8e2b1fd944b7456209b6bcea153c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `899e208b4e231417bf8168413ebc75de7aa8e2b1fd944b7456209b6bcea153c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 31 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the host FSBL, NFC, and PCIe MMIO state machines' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute the host FSBL, NFC, and PCIe MMIO state machines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the standalone PCIe contract runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute the standalone PCIe contract runner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:148:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute actual ARM prefetch and data abort entry paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute actual ARM prefetch and data abort entry paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:160:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the hardened NVMe IO callback service contract runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:171:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the crash-consistent FTL metadata contract runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl:229:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind persistent NFC media and fail closed outside silicon' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
