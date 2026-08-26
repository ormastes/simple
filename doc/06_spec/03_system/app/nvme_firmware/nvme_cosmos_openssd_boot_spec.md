# nvme_cosmos_openssd_boot_spec

> Executable hardware-independent evidence for the Cosmos+ OpenSSD
> `openssd2-8ch8way-v3.0.0` production-HAL design.

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

Source:
`test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl`

Run only with a current pure-Simple bootstrap runner:

```sh
bin/release/simple test \
  test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl \
  --mode=interpreter
```

`bin/release/simple` must be rebuilt/deployed from the current tree before this
spec is run; a stale binary with the obsolete `rt_env_set` ABI is not evidence.

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

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_pcie_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_pcie_auto_completion_test.shs
```

Requires exit `0`, no `FAIL`, and `cosmos PCIe contract: PASS`. It validates
HWH-bound IRQ `61` as level-high, stable endpoint snapshots, command FIFO plus
16-DW SRAM fetch, two-word AUTO completion with captured-slot release, and
direct/AUTO host-DMA FIFO ordering. CPU0 targeting is a local policy; IRQ `61` is only for
configuration/link/error state, not command arrival. Board IRQ delivery, DMA
data integrity, enumeration, reset, and recovery remain pending.

### 3. ARM prefetch/data abort contract

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_abort_contract_test.shs
```

Requires bounded QEMU execution, `prefetch: PASS`, `data: PASS`, and
`cosmos ARM prefetch/data abort contract: PASS`. It enters through the
production ARM vectors, checks captured syndrome/address/PC, and proves that
neither exception resumes. Physical-board abort behavior remains pending.

### 4. NVMe IO callback service contract

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_nvme_firmware_contract_test.shs
```

Requires exit `0`, no `FAIL`, `cosmos NVMe firmware contract: PASS`, and
`cosmos NVMe firmware ARM compile: PASS`. It covers bounded queue polling,
queue/slot/sequence/CID identity, SCT/SC/DNR completion status, exact
contiguous DMA span validation, distinct read/write media failures, basic Write
Zeroes, DSM Deallocate callback semantics, and retry only
before a provably uncommitted completion. The separate FTL scenario tests only
the metadata core.

### 5. FTL metadata contract

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_ftl_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_gc_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_discard_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_journal_reclaim_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_recovery_trim_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_transaction_recovery_test.shs
```

Requires all FTL host/ARM PASS pairs. It covers PPA geometry, journal ordering,
dual-checkpoint recovery, torn-tail handling, retirement guards,
fail-sticky ambiguous writes, 10% capacity reserve, bounded relocation, and
erase-after-move ordering. Additional focused checks cover durable discard,
64-bit journal reclamation, checkpoint trim-state reconstruction, whole-
transaction journal reservation, torn physical holes, and trailing allocation
recovery.

### 6. Persistent NFC media and startup composition

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_ftl_nfc_backend_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_nfc_io_fail_closed_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ftl_nfc_dma_isolation_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_ftl_media_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_ftl_physical_composition_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_media_tag_validation_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_ecc_refresh_test.shs
sh test/02_integration/os/cosmos/run_cosmos_ecc_refresh_build_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_storage_startup_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_storage_link_contract_test.shs
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

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_nvme_pcie_adapter_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_prp_control_test.shs
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

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_nvme_admin_contract_test.shs
```

Requires `cosmos NVMe admin contract: PASS` and
`cosmos NVMe admin ARM compile: PASS`. It covers bounded Identify,
SMART, queue lifecycle, Number-of-Queues features, Abort, AER, retry/latching,
and explicit Invalid Opcode for unsupported format and firmware commands. Edge
coverage includes Abort result bits, global NSID and maximum queue negotiation,
CQ IEN/IV, SQ QPRIO, and SMART NSID/RAE. It has no PCIe/PRP or persistent
media binding.

### 9. Single-owner NVMe dispatcher

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_nvme_dispatch_contract_test.shs
```

Requires the dispatcher host/ARM PASS pair. It fetches each controller FIFO
entry once, routes queue zero to admin and nonzero queues to IO, and prevents a
pending or terminal completion from consuming another command. Physical queue
register programming remains board-evidence work; UART foreground startup is
source-bound and ARM-compiled.

### 10. Host SMP, GIC, MMU, and cache

Runs:

```sh
sh test/02_integration/os/cosmos/run_cosmos_smp_cache_contract_test.shs
```

Requires exit `0`, no `FAIL`, and
`STATUS: PASS cosmos SMP/cache contract`. The driver checks cache set/way and
TTBR0 operands, SCU/ACTLR coherency ordering, GIC bounds, and the generation
tagged CPU1 release/ACK protocol.

### 11. Unbound QEMU boot

Runs:

```sh
COSMOS_BUILD_MODE=qemu \
  sh src/os/kernel/arch/arm32/cosmos/build.shs --run
```

The image must report `built build/os/simpleos_cosmos_openssd.elf (clean,
unbound, entry=...)`. Runtime,
MMU/L1/PL310, and primary GIC must report `OK`. CPU1 release, FSBL handoff,
NFC, and PCIe must report `UNAVAILABLE`. The terminal verdict must contain:

```text
COSMOS SOFTWARE HAL CHECKS PASS
COSMOS SILICON VALIDATION PENDING
```

`COSMOS SILICON HAL CHECKS PASS` and every `FAIL` marker are forbidden.

### 12. Exact bound silicon artifact

Runs:

```sh
COSMOS_BUILD_MODE=silicon \
COSMOS_SILICON_PROFILE=openssd2-8ch8way-v3.0.0 \
  sh src/os/kernel/arch/arm32/cosmos/build.shs
```

`readelf` and `nm` must prove ELF32 ARM `ET_EXEC`, a load segment, no unresolved
symbols, `.note.cosmos.profile`, and the global symbol:

```text
cosmos_profile_cosmos_plus_openssd2_8ch8way_v300
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

## Traceability

| Requirement | Executable evidence | Production status |
|-------------|---------------------|-------------------|
| REQ-001 | Host MMIO; bound silicon; QEMU unbound | Host checked |
| REQ-002 | Host NFC MMIO and geometry/command driver | Host checked |
| REQ-003 | Host NFC IO, ECC, timeout, quarantine | Host checked; board pending |
| REQ-004 | PCIe transport/IRQ/DMA, corrected bridge/admin runners; bound profile | Host checked; board pending |
| REQ-005 | QEMU runtime; ARM ABI edge scenario | Host checked |
| REQ-006 | Host SMP/GIC contract | Host checked; board pending |
| REQ-007 | Host MMU/cache contract; QEMU boot | Host checked; board pending |
| REQ-008 | Host FSBL/fail-closed MMIO; QEMU boot | Host checked; board pending |
| REQ-009 | Exact QEMU verdict; bound silicon build | Host checked; board pending |
| REQ-010 | Package positive/rejection self-test | Host checked |
| REQ-011 | All fourteen executable scenarios | Host checks passed individually; final SSpec blocked |
| REQ-012 | No executable claim; BT-001..BT-006 board campaign | **Board pending; excluded from `@req`** |
| NFR-001 | Host runners; bounded QEMU statuses | Host checked |
| NFR-002 | Host fail-closed cases; QEMU unbound; package rejection | Host checked |
| NFR-003 | Fail-closed host case, QEMU startup ordering, abort injection | Partial; board evidence pending |
| NFR-004 | Host NFC DMA/ECC/quarantine, PCIe DMA, and IO DMA-span contracts | Host checked; board pending |
| NFR-005 | Host SMP/cache coherency contract | Host checked; board pending |
| NFR-006 | ARM link closure and ABI edge scenario | Host checked |
| NFR-007 | ELF identity/profile note and package checks | Host checked |
| NFR-008 | Package manifest v3 source/board/tool/hash self-test | Software package provenance checked; board campaign environment pending |
| NFR-009 | Exact QEMU lane statuses and terminal verdict | Host checked |
| NFR-010 | This matrix plus all fourteen scenarios | Host checks passed individually; final SSpec blocked |
| NFR-011 | No executable claim; BT-003/BT-006 endurance campaign | **Board pending; excluded from `@req`** |
| NFR-012 | QEMU silicon-PASS rejection and this claim boundary | Host checked |

## Claim Boundary

Passing proves software behavior only. It does not prove physical NAND IO/ECC,
PCIe enumeration/MSI/DMA/reset, CPU1 coherency, BootROM/FSBL boot, power-loss
recovery, thermal behavior, or endurance. The board-only requirements
`REQ-012` and `NFR-011` are intentionally excluded from executable `@req`
traceability and remain pending until retained evidence from the identified
Cosmos+ board satisfies the production guide. Neither host, QEMU, compile,
synthetic Bootgen, source-check success, nor the host/ARM NVMe callback
contract runner can satisfy them.

## Current Execution Status

The runtime, MMIO, PCIe, NVMe IO, corrected PCIe bridge/admin, SMP/cache,
QEMU/silicon, and package results passed in scoped runs. Package manifest v3
binds clean source revision, complete build-source closure, board/boot/profile,
compiler/linker/Bootgen identities, DMA contract, and artifact hashes with a
standalone verifier and negative controls. Corrected coverage
includes admin Abort/queue/SMART fields, zero-write-only completion retry,
non-retryable post-start completion behavior, and PRP edges. Official Bootgen
v2026.1 and the pinned upstream bitstream are available locally, but no
identified-board execution receipt has been accepted. The latest strict bootstrap passed
Stage 2/3 sanity at 2,549,240 KiB peak RSS, then failed provenance because the
tracked dirty state changed during measurement. A focused Stage 4 continuation
cleared the address-of parser failure and segfaulted in
`HirLowering.lower_trait` during HIR import resolution at 2,976,672 KiB peak
RSS. A null imported-trait payload is the leading hypothesis. There is no
current deployed `bin/release/simple`, so the fourteen-scenario SSpec and
generated manual have
not been executed/generated with the current tree. Production is therefore
**BLOCKED/FAIL**, not accepted. Current SSpec/docgen and physical board proof
remain open.
