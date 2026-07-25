# Cosmos+ OpenSSD Production Firmware Port Plan

**Created:** 2026-06-30
**Updated:** 2026-07-26
**Target:** CRZ Cosmos+ OpenSSD, Xilinx Zynq-7000 XC7Z045, dual Cortex-A9
**Upstream PL baseline:** Cosmos+ OpenSSD 8Ch8Way v3.0.0 at commit
`78601486bb5581e40628ec7e841dea8e97eff034`
**Current status:** host/QEMU bring-up works; production host mocks, immutable
profile binding, and all board acceptance are pending.

## Objective

Deliver a reproducible, fail-closed Cosmos+ firmware image whose ARM runtime,
MMU/cache, SMP/GIC, FSBL handoff, 8-channel/8-way NAND controller, PCIe/NVMe
endpoint, and Bootgen package are verified at the correct evidence level. Do
not label compilation or QEMU as silicon success.

## Implemented Software

| Area | Current implementation |
|---|---|
| Entry/faults | ARM vector table, VBAR, primary/secondary stacks, prefetch/data abort capture and terminal park |
| Runtime | Freestanding memory/string and ARM EABI division/memory support with edge self-test |
| Memory/cache | 16 KiB section table, DDR/device/OCM attributes, SCU, `ACTLR.SMP`, L1 set/way maintenance, CPU0 PL310 |
| GIC/SMP | GICv1 distributor/CPU interfaces, Zynq CPU1 `0xFFFFFFF0` release, generation mailbox, post-MMU/GIC ACK |
| FSBL | Read-only SLCR clock/reset/lock and `PCFG_DONE` handoff validation |
| NFC | Upstream Tiger4NSC 8x8 registers, init, status, read/program/erase, ECC decode, DMA checks, bounded channel quarantine |
| PCIe | Upstream host aperture/status/function/NVMe/admin registers, stable bounded readiness snapshots |
| Integration | Bounded dual UART, dependency gating, distinct QEMU/silicon verdicts |
| Packaging | Explicit inputs, strict ELF/bitstream/Bootgen validation, canonical alias rejection, hash manifest |

The firmware-facing platform descriptor remains
`src/os/kernel/arch/arm32/platform/cosmos_openssd.spl`. The actual HAL and
packager are under `src/os/kernel/arch/arm32/cosmos/`.

## Upstream Register Binding

NFC uses eight `0x10000` channel apertures from `0x43C00000` through
`0x43C7FFFF`. Commands are upstream uProgROM entries, not generic NAND opcodes.
The verified upstream `OpenSSD2.bit` hash recorded by the source contract is:

```text
66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2
```

PCIe uses the upstream CPU aperture at `0x83C00000`, span `0x10000`, with
status/function at `0x100/0x104`, NVMe state at `0x200`, admin queue state at
`0x21C`, and IO SQ/CQ windows at `0x220/0x260`. Host-visible identity is
`10EE:7028`, class `010802`, BAR0 size 8 KiB.

Neither PL block has a trustworthy runtime identity register. Production must
bind the exact bitstream hash to:

```text
COSMOS_NFC_PACKAGE_VERIFIED_OPENSSD2_8C8W_3_0_0
COSMOS_NFC_DMA_IDENTITY_BASE
COSMOS_NFC_DMA_IDENTITY_END
COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS
COSMOS_PCIE_BITSTREAM_CONTRACT=COSMOS_PCIE_CONTRACT_8CH8WAY_V300
```

The generic silicon build does not currently supply these values and therefore
remains fail-closed/unbound. Connecting one immutable platform manifest to both
build and package is a release blocker.

## Current Host Evidence

On 2026-07-26:

```sh
COSMOS_BUILD_MODE=qemu sh src/os/kernel/arch/arm32/cosmos/build.shs --run
```

produced ELF32 ARM entry `0x100000` and:

```text
COSMOS+ OpenSSD (Zynq-7000 / Cortex-A9) boot OK
[cosmos] ARMv7 runtime: OK
[cosmos] MMU/L1/PL310: OK
[cosmos] GIC primary: OK
[cosmos] CPU1 release: UNAVAILABLE
[cosmos] FSBL handoff: UNAVAILABLE
[cosmos] NFC PL: UNAVAILABLE
[cosmos] PCIe PL: UNAVAILABLE
COSMOS SOFTWARE HAL CHECKS PASS
COSMOS SILICON VALIDATION PENDING
```

The packager self-test also passed:

```sh
sh src/os/kernel/arch/arm32/cosmos/package_boot.shs --self-test
```

This proves QEMU software bring-up and package validation logic only. It does
not execute silicon MMIO or BootROM.

## Production Work Breakdown

### Phase A - Host Closure

1. Add immutable build/package manifest binding exact bitstream hash, NFC/PCIe
   tokens, DMA reservation, repository revision, and tool versions.
2. Add executable host mock-MMIO/event tests for FSBL, NFC, PCIe, GIC/SMP,
   MMU/cache/PL310, UART timeout, and abort ordering.
3. Replace static source guards with behavioral assertions where a mock can
   observe reads, writes, barriers, events, timeout, and terminal faults.
4. Rebuild the pure-Simple release runner with the current runtime ABI; do not
   accept the stale `rt_env_set` crash as a test result.
5. Run each H0/H1 gate once and retain logs/hashes.

**Exit:** ST-001..ST-012 pass with no board claim.

### Phase B - Board Boot and Inventory

1. Record operator, UTC, board serial/revision, Zynq marking, DRAM/NAND part
   numbers, boot mode, host/kernel/tools, power supply, and power-cut fixture.
2. Verify FSBL, bitstream, firmware, `boot.bin`, and manifest SHA-256 before
   flashing.
3. Cold boot through BootROM/FSBL, capture complete serial, and confirm the
   manifest-matching silicon image reaches all required `OK` statuses.
4. Repeat warm reset and power-cycle boot; preserve reset-cause/serial evidence.

**Exit:** BT-001 passes. A serial marker without matching hashes does not pass.

### Phase C - NAND and Recovery

1. Reserve documented destructive-test blocks outside production metadata/data.
2. Inventory all 8 channels x 8 ways and reject missing/aliased targets.
3. For each target, erase one reserved block, program/read every page with
   all-zero, all-one, address, checkerboard, walking-bit, and seeded-random
   patterns; compare data and spare.
4. Exercise ECC at zero, correctable, refresh-threshold, declared strength, and
   uncorrectable levels using a supported injection method; verify status and
   no silent corruption.
5. Force command timeout and verify channel quarantine and DMA non-reuse.
6. Interrupt power at declared erase, program, journal, flush, and completion
   boundaries. Reboot and verify metadata, acknowledged data, and media state.
7. Run thermal/endurance/scrub campaign with predeclared duration/counts.

**Exit:** BT-002, BT-003, BT-006 NAND portions pass with zero silent mismatch.

### Phase D - PCIe/NVMe

1. Capture `lspci -nnvv -s <BDF>` and verify `10ee:7028`, class `0108`, BAR0
   8 KiB, Bus Master, MSI enabled, MSI-X disabled, and expected link state.
2. Capture `nvme list`, `nvme id-ctrl`, `nvme id-ns`, queue/controller logs, and
   kernel messages.
3. Run admin and multiple IO queue traffic against a disposable namespace;
   verify completions, interrupt counts, DMA checksums, queue wrap/phase, and
   mixed read/write integrity.
4. Test controller reset, function reset where supported, PERST/cold reset, link
   retrain, and recovery while idle and under controlled IO.
5. Run sustained mixed IO concurrently with NAND and CPU1 stress.

**Exit:** BT-004 and PCIe portions of BT-006 pass without AER, lost completion,
silent corruption, or unrecovered reset.

### Phase E - SMP, GIC, and Cache

1. Verify CPU1 READY/RELEASED/ACK generation and timeout/cancel behavior.
2. Route and count SGI, PPI, and representative SPI delivery to each core.
3. Run shared cache-line ping-pong with sequence/checksum validation.
4. Exercise clean/invalidate boundaries and PL DMA visibility in both
   directions using the reserved uncached region and separate cached buffers.
5. Run the stress concurrently with NAND and PCIe traffic.

**Exit:** BT-005 passes with no stale data, generation mismatch, duplicate/lost
interrupt, lockup, or DMA coherency failure.

## Required Evidence Bundle

Use a new immutable directory per campaign:

```text
evidence/cosmos/<UTC>-<board-serial>/
  inventory.txt
  commands.log
  tools.txt
  artifacts.sha256
  boot.bin.manifest
  serial/
  nand/
  pcie/
  smp-cache/
  power-loss/
  thermal-endurance/
  result.md
```

`result.md` maps ST/BT IDs and every REQ/NFR to PASS/FAIL/PENDING plus evidence
paths. Raw logs are retained; summaries do not replace them.

## Release Gate

Release requires:

- all ST-001..ST-012 and BT-001..BT-006 PASS;
- exact build-to-bitstream profile binding;
- no unresolved symbols, FAIL marker, abort, unbounded wait, stale runner, or
  unreviewed register assumption;
- independent final review of source and evidence bundle.

Until then, the only valid statement is:

> Cosmos+ host/QEMU bring-up is demonstrated; physical production acceptance is
> pending.
