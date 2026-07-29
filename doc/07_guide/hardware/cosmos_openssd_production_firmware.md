# Cosmos+ OpenSSD Production Firmware Guide

## Purpose

This guide builds, packages, and validates the Cosmos+ OpenSSD Zynq-7000
firmware without confusing host evidence with physical acceptance. It applies
to the upstream 8-channel/8-way v3.0.0 PL contract at commit
`78601486bb5581e40628ec7e841dea8e97eff034`.

Production requires all host and board gates below. Current production status
is **BLOCKED/FAIL**: the persistent NFC backend, media adapter, and UART
foreground dispatcher are implemented and ARM-compiled, and a pinned FSBL/
Bootgen package exists, but fresh SSpec/docgen and all board evidence remain
pending.

## Safety

- NAND tests are destructive. Use only explicitly reserved test blocks on a
  board whose contents may be lost.
- Power-loss and reset tests require a controlled fixture. Do not remove power
  manually while probes, JTAG, or host links are in an unsafe state.
- Record the board and artifact identity before the first write.
- Stop on an abort, unknown register value, missing target, timeout, hash
  mismatch, overheating, unexpected reset, AER error, or data mismatch.

## Factory-Initialize Blank NAND

Normal boot never formats NAND. On a board whose main and metadata NAND are
already confirmed erased, let boot reach `NVMe storage: UNAVAILABLE`, halt CPU0
with JTAG, call `cosmos_storage_factory_initialize_erased()`, and require
`COSMOS_OK`. Reset immediately afterward; normal boot must then mount and
recover the two initial checkpoints. Never call this symbol on media containing
user data.
- After an NFC timeout, do not reuse its DMA buffers or channel until platform
  reset.
- QEMU output is never board acceptance.

## Source and Register Baseline

The HAL is tied to these upstream sources:

- NFC software: `GreedyFTL-3.0.0/nsc_driver.h`,
  `nsc_driver.c`, `ftl_config.h`, and `request_schedule.c`.
- NFC RTL: Tiger4 `Dispatcher.v`, `Decoder.v`,
  `CompletionDataChannel.v`, and `BCHDecoderOutputControl.v`.
- Hardware handoff: `OpenSSD2-8C8W-Prebuild-3.0.0.hdf` and its HWH.
- PCIe software/RTL: `nvme/host_lld.h`,
  `nvme_host_ctrl_8lane-1.0.0/s_axi_reg.v`, and the PCIe `.xci`.
- Zynq PS/SMP/boot: AMD UG585.
- PCIe endpoint behavior: AMD PG054.

The accepted upstream bitstream hash recorded by the NFC source is:

```text
66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2  OpenSSD2.bit
```

Rebuilding Vivado output changes the trust boundary. Review the generated
address map and relevant RTL/software and approve a new hash before use.

## Contract Summary

### NFC

- Eight channels: `0x43C00000 + channel * 0x10000`.
- Eight ways per channel.
- 16 KiB page data, 256-byte spare, 256 rows/block.
- LUN0 `0x000000..0x1057FF`; LUN1 `0x200000..0x3057FF`.
- Commands: reset 1, set-features 6, read trigger 13, read transfer 18,
  program 28, erase 37, status 41.
- Completion: `0xA5000001`.
- ECC validity: CRC bit 28, spare bit 24, page word 1 `0xFFFFFFFF`;
  worst chunk errors in bits 23:16; refresh when greater than 20.

NFC IO is disabled unless the exact package token and all reserved uncached DMA
values are compiled in.

### PCIe

- CPU aperture `0x83C00000`, span `0x10000`.
- Status `0x100`, function `0x104`, NVMe state `0x200`, admin queues `0x21C`,
  IO SQ `0x220`, IO CQ `0x260`.
- Endpoint `10EE:7028`, NVMe class `010802`, BAR0 8 KiB.
- Required readiness: link up, stable snapshot, Bus Master, MSI, valid state.
- Rejected: undefined bits, MSI-X, MME > 3, partial admin queue state, ready
  without enabled controller/queues, and state while disabled.
- HWH binding: `NVMeHostController_0/dev_irq_assert` is GIC ID `61`, active-high
  level. CPU0 targeting is a local policy that requires board confirmation.
- IRQ `61` reports configuration/link/error state, not command arrival. Commands
  are polled from the command FIFO; it must never be used as an IO-work signal.
- Transport: command FIFO metadata plus 16-DW SRAM command payload, three-word
  completion publication, and bounded direct/AUTO host-DMA FIFOs.

PCIe MMIO is disabled unless
`COSMOS_PCIE_BITSTREAM_CONTRACT=COSMOS_PCIE_CONTRACT_8CH8WAY_V300`.

## Profile Binding

Three profile states matter:

1. `qemu`: safe host emulation; optional hardware remains unavailable.
2. `silicon-unbound`: compiles silicon paths but cannot access NFC/PCIe.
3. `silicon-bound`: exact bitstream hash, NFC/PCIe tokens, and reserved uncached
   DMA interval come from one immutable platform manifest.

Only state 3 may be flashed for production acceptance. The repository emits
the bound profile identity and package receipt, and the pinned package below
has real Bootgen output. Production acceptance still requires identified-board
provenance and retained board evidence. Do not work around the gates by
defining tokens manually without a verified artifact and evidence record.

The shared NVMe firmware has explicit Simple-simulator, QEMU/RAM-NAND,
OpenSSD 2Ch8Way/8Ch8Way, and KV260/FPGA profiles. QEMU firmware parity passes;
KV260 and physical OpenSSD availability remains fail closed pending their
hardware gates. New targets add a profile and evidence adapter rather than
forking the command, FTL, or recovery core.

The production manifest must include at least:

```text
format=cosmos-zynq-boot-v3
board=cosmos-plus-openssd
board.serial=<serial>
board.revision=<revision>
boot.mode=sd
profile=cosmos-plus-openssd2-8ch8way-v3.0.0
source.revision=<jj-or-git-revision>
source.dirty=false
bitstream.contract=openssd2-8ch8way-v3.0.0
bitstream.contract.token=0x00030000
bitstream.sha256=<verified-hash>
nfc.dma.base=<hex>
nfc.dma.end=<hex>
nfc.toggle_payload=<hex>
fsbl.sha256=<hash>
firmware.sha256=<hash>
boot.sha256=<hash>
tool.clang.version=<version>
tool.clang.sha256=<hash>
tool.lld.version=<version>
tool.lld.sha256=<hash>
tool.bootgen.version=<version>
tool.bootgen.sha256=<hash>
```

The receipt/self-test records and checks full compiled-source closure,
compiler/linker identity, clean repository revision, board/profile identity,
boot mode, canonical artifact snapshots, hashes, contract/DMA identity, and
strict ELF/Bootgen metadata. `--verify-manifest` rechecks required unique fields,
artifact hashes, and that the current clean checkout matches `source.revision`.
Physical board execution remains external H2 evidence.

## Host Prerequisites

Required commands:

```sh
export PATH="$PWD/build/tools/bin:$PATH"
clang --version
ld.lld --version
readelf --version
nm --version
qemu-system-arm --version
bootgen -help
sha256sum --version
realpath --version
```

Current local tool/input evidence:

- Xilinx Bootgen source commit:
  `eb7256bca6825a1a002cb4d9779d178060036bb0`
- Bootgen v2026.1 binary SHA-256:
  `245ca33cee696db58823870f22d6575949a25579e7aab66f3537333cfebc4e80`
- pinned HDF SHA-256:
  `03481b19742a3ed8d051dd0ce777e956b446d3986baa05395be5714fcd4b88ba`
- extracted `OpenSSD2.bit` SHA-256:
  `66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2`

Use `bin/release/simple` rebuilt and deployed from the current tree. A stale
release binary that links the obsolete two-argument `rt_env_set` ABI can crash
before an SSpec runs and is not evidence. There is currently no accepted
deployed runner. The unchanged-tree strict run passed Stage 2/3 sanity and
cleared the prior parser/HIR crashes. Retry 14 then rebuilt the Rust authority,
compiled all Stage 2 objects, and failed at the native link after 24m01s on
three stale symbol groups: an undeclared trait-lowering helper, removed
coverage-inventory calls, and CUDA sizing lowered to unavailable bare `sum`.
Its peak RSS was 2,591,760 KiB with zero swap. Retry 15 is the next bounded
admission attempt; complete it before using `bin/release/simple`.

## Host Build and QEMU Gate

From the repository root:

```sh
COSMOS_BUILD_MODE=qemu sh src/os/kernel/arch/arm32/cosmos/build.shs --run
readelf -hW build/os/simpleos_cosmos_openssd.elf
test -z "$(nm -u build/os/simpleos_cosmos_openssd.elf)"
```

The exact successful QEMU transcript observed on 2026-07-26 was:

```text
built build/os/simpleos_cosmos_openssd.elf (clean, unbound, entry=0x100000, receipt=...)
=== boot on qemu xilinx-zynq-a9 (UART1 -> stdio) ===
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

`timeout` terminating QEMU after the firmware parks in WFI is expected. Any
different status, missing PENDING marker, or any FAIL/abort marker fails.

Build the unbound silicon artifact without executing it:

```sh
COSMOS_BUILD_MODE=silicon sh src/os/kernel/arch/arm32/cosmos/build.shs
readelf -hW build/os/simpleos_cosmos_openssd_silicon.elf
test -z "$(nm -u build/os/simpleos_cosmos_openssd_silicon.elf)"
```

This proves compilation only. It is not a flash-ready bound image.

## System and Package Gate

Run:

```sh
bin/release/simple test \
  test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl \
  --mode=interpreter

sh src/os/kernel/arch/arm32/cosmos/package_boot.shs --self-test
```

The package provenance self-test ends with:

```text
COSMOS_PACKAGE_PROVENANCE_PASS source=clean board=bound tools=clang,lld,bootgen artifacts=fsbl,bitstream,firmware,boot
STATUS: PASS cosmos-package-boot self-test
```

It checks positive and rejection fixtures, including ELF type/entry/segments,
silicon/QEMU identity, bitstream sync, Bootgen headers/metadata, empty/truncated
output, failure, and canonical aliases. Its fake Bootgen and synthetic artifacts
also reject missing provenance and mismatched hashes. They do not prove BootROM
boot or matching PL logic.

## Required Host Mock-MMIO Gate

The H1 gate is implemented by the following runners and must pass before board
work is accepted as release evidence:

```sh
sh test/02_integration/os/cosmos/run_cosmos_hal_mmio_test.shs
sh test/02_integration/os/cosmos/run_cosmos_abort_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_runtime_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_pcie_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_firmware_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_pcie_adapter_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_admin_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_smp_cache_contract_test.shs
```

The test-only backends record reads, writes, barriers, and terminal events while
production continues to use direct volatile MMIO. The runners prove:

1. FSBL evaluates every lock/clock/reset/`PCFG_DONE` predicate and performs no
   NFC/PCIe read after failure.
2. NFC validates topology, rows, erase alignment, DMA bounds/overlap, status,
   ECC, channel serialization, completion, timeout, and quarantine.
3. PCIe handles link progression, link loss between samples, Bus Master/MSI,
   IRQ-61 W1C handling, command FIFO/SRAM fetch, completion publication, and
   direct/AUTO host-DMA FIFO ordering.
4. CPU1 vector write occurs before DSB/SEV; generation ACK occurs only after
   secondary MMU and GIC success; timeout cancels.
5. MMU descriptors, SCU/`ACTLR.SMP` order, cache set/way operands, and PL310
   completion/timeout are correct.
6. Runtime ABI covers memory/string/EABI division edges and no unresolved
   host/ARM runtime symbols; UART wait is bounded and startup failure is terminal.
7. NVMe IO preserves queue/slot/sequence/CID, validates SCT/SC/DNR and exact
   DMA spans, distinguishes read/write media failures, supports Write Zeroes,
   DSM Deallocate, FUA, and LR, and fails closed on ambiguous completion.
8. The bridge decodes DW0/DW1/DW6..DW12; controller AUTO DMA walks direct PRP2
   and PRP-list transfers. The NFC backend and media adapter provide the
   production callback binding.
9. Bounded QEMU injections execute the production ARM prefetch/data-abort
   vectors and verify syndrome/address/PC capture plus terminal non-resumption.

The runtime ABI, PCIe, NVMe IO, corrected PCIe bridge/admin, MMIO, and SMP/cache
runners passed in their scoped H1 runs. Corrective evidence covers Abort result
bits, Number-of-Queues NSID/max, CQ IEN/IV, SQ QPRIO, SMART NSID/RAE,
zero-write-only completion retry, non-retryable post-start completion, and PRP
edges. The FTL path now covers explicit persistent wire formats, dual
checkpoints, journal reclamation, tagged NAND data, bounded relocation, and
foreground UART dispatch. These objects compile for both profiles. ECC refresh
relocation has focused host/ARM evidence; physical correction margin and
persistence behavior still require board evidence. MMU W^X small pages passed
host/SMP contracts and QEMU plus silicon builds. Official Bootgen v2026.1 is
built at `build/tools/bin/bootgen`; the pinned HDF and `OpenSSD2.bit` hashes
match the profile. The vendor HSI flow produced FSBL SHA-256
`baa40ab19de0b14c7851b96385c3b7b281637adfff5ad58f6671ca27f547d351`.
Real packaging passed with firmware SHA-256
`5362d5c91551e2b379a6e7a321a112d4604bf91cd6447d27410ca2f4365bbbcb`,
boot SHA-256
`c55a679486fdd89cbf1f7f59cae9e1cda4379328e9c429bcbb09c75d8e6191bc`,
and manifest SHA-256
`55efec43c8c59f44fb99498ee380af13bd03d0c2d925bf4acef7e541091ba67a`.
Do not represent these host/ARM results as physical persistence or board proof.

## Current Software Gate

Do not execute the fourteen-scenario SSpec with a stale binary. Retry 15 admitted
a pure-Simple Stage 2 bootstrap compiler and used it to build the restored
89,668-byte RV32 RAM-NAND firmware. The source-matched gate passes behavioral
GHDL, full AXI RAM with 847 reads/461 writes in the exact 256-byte region, and
clean plus garbage-filled synthesizable BRAM; each observation capture matches
its own live UART stream. Stage 2 is sufficient for native-build/GHDL
but intentionally lacks `run`/`test`; Stage 3 reached its bounded timeout after
the Rust environment boundary was fixed to reject embedded NULs. Final SSpec
and generated-manual evidence therefore still require a current full CLI.

Before production can move from **BLOCKED/FAIL**, complete:

1. One current pure-Simple SSpec run/docgen when a current runner is available.
2. Execute and retain the BT-001..BT-006 board campaign with the pinned package.
   REQ-012 and NFR-011 remain board-only.

After the runner blocker is solved, execute the consolidated host gate:

```sh
SIMPLE_BINARY=bin/release/simple \
  sh scripts/check/check-nvme-firmware-remaining-gates.shs --post-bootstrap
```

An optional UNO Q portability build is supplementary only:

```sh
SIMPLE_BINARY=bin/release/simple \
  sh scripts/check/check-nvme-firmware-remaining-gates.shs --uno-q-build
```

Physical execution remains postponed until the target environment exists. The
retained campaign can then be checked without running destructive commands:

```sh
sh scripts/check/check-nvme-firmware-remaining-gates.shs \
  --board-evidence evidence/cosmos/<UTC>-<board-serial>
```

## Build the Board Package

First verify immutable inputs:

```sh
sha256sum path/to/fsbl.elf path/to/OpenSSD2.bit \
  build/os/simpleos_cosmos_openssd_silicon_bound.elf
```

Then package:

```sh
sh src/os/kernel/arch/arm32/cosmos/package_boot.shs \
  --fsbl path/to/fsbl.elf \
  --bitstream path/to/OpenSSD2.bit \
  --elf build/os/simpleos_cosmos_openssd_silicon_bound.elf \
  --board-serial <board-serial> \
  --board-revision <board-revision> \
  --boot-mode sd \
  --output build/os/cosmos-production-boot.bin

sh src/os/kernel/arch/arm32/cosmos/package_boot.shs \
  --verify-manifest build/os/cosmos-production-boot.bin.manifest
sha256sum build/os/cosmos-production-boot.bin \
  build/os/cosmos-production-boot.bin.manifest
bootgen -arch zynq -read build/os/cosmos-production-boot.bin
```

Do not use the current unbound silicon ELF in this command. Compare the
manifest against the approved profile before flashing.

## Start an Evidence Campaign

Create an immutable campaign directory before touching hardware:

```sh
campaign="evidence/cosmos/$(date -u +%Y%m%dT%H%M%SZ)-<board-serial>"
mkdir -p "$campaign"/{serial,nand,pcie,smp-cache,power-loss,thermal-endurance}
```

Record:

```text
operator and UTC
board serial/revision and Zynq marking
DRAM and all NAND part numbers
boot switches/source
power supply and cutoff fixture
host hardware, kernel, PCIe slot, and BDF
JTAG/debug probe and versions
repository revision and dirty state
compiler/linker/Bootgen/QEMU/nvme-cli/fio versions
all artifact hashes and package manifest
```

Write every command and exit code to `commands.log`. Keep raw logs; a summary is
not a substitute.

Before review, retain nonempty regular files `inventory.txt`, `commands.log`,
`tools.txt`, `artifacts.sha256`, `boot.bin.manifest`, `result.md`, and
`manifest.txt`. `manifest.txt` uses `schema=cosmos-board-campaign-v1`,
`status=pass`, clean source revision, board identity, boot mode, distinct
operator/reviewer, UTC start/end, power fixture, PCIe host/BDF, destructive
block range, package artifact hashes, and SHA-256 values for every top-level
evidence file. The package manifest must be the original v3 manifest with its
referenced artifacts still available; the checker runs `--verify-manifest`
against the current clean source.

Use these exact campaign keys; every `*.sha256` value is lowercase hex:

```text
schema=cosmos-board-campaign-v1
status=pass
board.serial=<serial>
board.revision=<revision>
source.commit=<40-or-64-hex-clean-revision>
source.dirty=false
boot.mode=sd
operator=<operator-id>
reviewer=<different-reviewer-id>
started_utc=YYYY-MM-DDTHH:MM:SSZ
completed_utc=YYYY-MM-DDTHH:MM:SSZ
power.fixture=<fixture-id>
pcie.host=<host-id>
pcie.bdf=0000:01:00.0
destructive.blocks=<predeclared-range>
package.fsbl.sha256=<sha256>
package.bitstream.sha256=<sha256>
package.firmware.sha256=<sha256>
package.boot.sha256=<sha256>
package.manifest.sha256=<sha256-of-boot.bin.manifest>
evidence.inventory.sha256=<sha256-of-inventory.txt>
evidence.commands.sha256=<sha256-of-commands.log>
evidence.tools.sha256=<sha256-of-tools.txt>
evidence.artifacts.sha256=<sha256-of-artifacts.sha256>
evidence.result.sha256=<sha256-of-result.md>
```

## BootROM and FSBL Acceptance

1. Set the documented board boot mode and connect UART/JTAG/power measurement.
2. Flash or place the exact manifest-matching `boot.bin` using the board's
   approved method.
3. Power off fully, wait for rails to discharge, start serial capture, then
   power on.
4. Confirm BootROM selects the intended device, FSBL loads the bitstream and
   firmware, and no fallback image is used.
5. Verify FSBL handoff reports `OK`: SLCR locked, ARM/DDR clocks active, PS and
   CPU0 reset clear, and `PCFG_DONE`.
6. Verify every silicon lane reports `OK` and the only terminal verdict is:

```text
COSMOS SILICON HAL CHECKS PASS
```

7. Repeat a warm reset and at least one full cold power cycle. Capture complete
   serial, reset reason, and artifact hashes each time.

Fail on any abort, unavailable/invalid/timeout/hardware error, missing line,
unexpected image, hash mismatch, or boot requiring manual debugger repair.

## NAND Inventory and Destructive Test

Before execution, document reserved destructive-test blocks that cannot overlap
boot, firmware, FTL metadata, bad-block tables, journals, or user namespaces.

For each of 64 `(channel, way)` targets:

1. Reset and enter toggle mode; record ready/busy and controller-idle timing.
2. Read NAND identity/geometry through the supported board diagnostic and
   compare it to the approved part/geometry. Stop on alias or missing target.
3. Select a known-good reserved block. Preserve original bad-block markers.
4. Erase and verify status.
5. Program and read every page with these deterministic patterns:
   all `00`, all `FF`, address-derived, `AA/55`, walking one/zero, and a stored
   seeded pseudorandom stream.
6. Compare all 16 KiB data and 256 spare bytes; record status and all 11 ECC
   words for every read.
7. Verify boundary rejection: LUN gap, last valid row, first invalid row, and
   non-block-aligned erase must not issue hardware commands.
8. Force a bounded timeout with the test fixture; verify the channel is
   quarantined and supplied DMA regions are not reused until reset.

Any silent mismatch, incorrect target, lost bad-block marker, or operation after
quarantine fails the campaign.

## NAND ECC Acceptance

Record the actual BCH strength and injection mechanism from the approved
bitstream. On one reserved block per target, inject:

- zero errors;
- one correctable error;
- exactly 20 errors in the worst chunk;
- 21 errors to trigger refresh;
- the declared correction limit;
- one more than the correction limit.

Verify corrected data byte-for-byte, CRC/spare/page validity, worst-chunk count,
refresh decision, and explicit uncorrectable failure. If the hardware cannot
inject deterministic errors, use a reviewed RTL/test bitstream with its own
hash and do not treat normal wear observations as equivalent.

## NAND Power-Loss Acceptance

Use a programmable cutoff triggered from firmware/logic analyzer. Predeclare
iteration counts and cutoff offsets before starting. Exercise:

1. erase command accepted but not complete;
2. program command accepted but not complete;
3. data complete before NAND status;
4. journal append before/after durable marker;
5. namespace flush before/after completion;
6. background relocation/scrub metadata update.

After every cutoff:

- cold boot through BootROM/FSBL without debugger repair;
- run recovery and inventory;
- verify previously acknowledged data and expected atomicity;
- verify interrupted operations are either committed or rejected, never
  silently mixed;
- verify bad-block/media retirement and journal state;
- retain serial, power trace, command history, hashes, and data checksums.

Zero silent acknowledged-data loss is required.

## PCIe Enumeration and BAR Acceptance

On the Linux host, identify the BDF and collect:

```sh
lspci -Dnn | grep -i '10ee:7028'
lspci -Dnnvv -s <BDF>
cat /sys/bus/pci/devices/0000:<BDF>/resource
dmesg -T | tail -n 500
```

Verify:

- vendor/device `10ee:7028`;
- class `0108`/NVMe;
- BAR0 assigned and 8 KiB;
- link reaches expected width/speed and remains stable;
- Bus Master enabled;
- MSI enabled, MSI-X disabled, MME no greater than 3;
- no uncorrected AER or surprise-down event.

The firmware's CPU-side `0x83C00000` aperture is not the host BAR address.

## NVMe Queue, MSI, and DMA Acceptance

Collect:

```sh
nvme list
nvme id-ctrl /dev/nvmeX
nvme id-ns /dev/nvmeX -n 1
nvme get-log /dev/nvmeX --log-id=1 --log-len=64
grep -E 'nvme|<BDF>' /proc/interrupts
```

Against a disposable test namespace:

1. Execute Identify, Get Log, Set/Get Features, and queue create/delete paths.
2. Run one queue, then the supported multi-queue count; cross queue-depth and
   wrap/phase boundaries.
3. Compare deterministic and seeded-random data after DMA read/write.
4. Verify interrupt count/completion mapping and no lost/duplicate completion.
5. Run mixed read/write/flush with direct IO using a recorded `fio` job file,
   verify its data, and retain the exact job and JSON output.
6. Monitor AER, controller status, queue state, temperature, and error logs.

Do not run destructive IO against an unapproved namespace.

## PCIe Reset and Link Recovery

While idle and at controlled IO boundaries, test:

```sh
nvme reset /dev/nvmeX
test -w /sys/bus/pci/devices/0000:<BDF>/reset &&
  echo 1 | sudo tee /sys/bus/pci/devices/0000:<BDF>/reset
```

Also exercise PERST/cold power reset and host-supported link retrain/hot reset.
After each event, verify re-enumeration, BAR/MSI state, admin/IO queue
recreation, no stale DMA, and data integrity. An unrecovered controller, AER
fatal error, stale completion, or silent mismatch fails.

## SMP, GIC, and Cache Acceptance

Use a board diagnostic image built from the same bound profile:

1. Capture CPU1 READY, RELEASED generation, and matching ACK. Exercise a forced
   secondary initialization failure and verify CANCELLED/timeout without CPU0
   lockup.
2. Send counted SGIs both directions; route representative PPIs and SPIs; prove
   exact interrupt counts and EOI behavior on each core.
3. Ping-pong ownership of aligned shared cache lines with monotonically
   increasing sequence and checksum for the predeclared stress duration.
4. Exercise cached producer/consumer buffers across both cores.
5. Exercise PS-to-PL and PL-to-PS DMA with reserved uncached identity buffers;
   separately verify explicit maintenance for any cached DMA test buffers.
6. Run CPU1/GIC/cache stress concurrently with NFC and PCIe queue traffic.

Fail on stale data, sequence gap, duplicate/lost interrupt, generation mismatch,
unexpected CPU park, timeout, abort, or checksum error.

## Thermal and Endurance Acceptance

Before the run, record ambient limits, airflow, temperature source, duration,
IO mix, queue depths, power-cycle count, NAND cycle budget, and stop limits.
During the run retain periodic:

- controller/board temperature;
- NAND corrected/uncorrectable ECC and refresh/scrub counts;
- media retirement/bad-block changes;
- PCIe link/AER and NVMe error/SMART logs;
- interrupt/DMA/queue progress;
- reset and power-loss outcomes.

Never shorten a declared run after a failure. Stop safely on thermal or power
limits and report FAIL/PENDING rather than discarding the interval.

## Evidence Review

Create `result.md` with one row for every ST/BT scenario and REQ/NFR:

```text
ID | PASS/FAIL/PENDING | command/procedure | raw evidence path | SHA-256 | reviewer
```

For BT-001..BT-006, use exactly one `PASS` row per ID. Raw paths must be
relative, remain inside the campaign, and name nonempty regular files. Hashes
are tamper evidence, not protection from a malicious local owner; production
acceptance still requires the independent reviewer.

Production PASS requires, after the current software blockers are resolved:

- ST-001..ST-019 and BT-001..BT-006 all PASS;
- exact source/FSBL/bitstream/firmware/boot hashes;
- immutable profile binding and reserved DMA proof;
- no abort, timeout, unknown status, FAIL marker, silent data mismatch, stale
  runner, or unexplained log gap;
- independent review of source and evidence.

Current report:

> Cosmos+ software integration and a pinned FSBL/real package are present, but
> production is BLOCKED/FAIL pending fresh pure-Simple SSpec/docgen and retained
> board evidence.
