# Cosmos+ OpenSSD Production HAL Architecture

## Decision

Use one freestanding, statically linked ARMv7 image with direct platform-owned
MMIO and compile-time profile binding. Keep QEMU and silicon behavior in the
same modules, but make optional PL access impossible unless the selected
bitstream contract is verified. Retain a single boot coordinator and a single
five-value status model.

The explicit compiler target `armv7-unknown-none-eabi` is the Cosmos Cortex-A9
soft-float profile. The compiler must emit CPU `cortex-a9`, reject Cortex-A7,
VFPv4, or VFP-register ABI attributes, and retain the exact two production
exports/two-C-bridge FSBL dependency closure before the object may enter the
firmware link. Internal outcome accessors are not HAL APIs; only coverage-test
C builds expose reset/snapshot wrappers for them.

This avoids a runtime device-discovery abstraction that the upstream PL does
not support: neither Tiger4NSC nor NVMeHostController exposes a trustworthy IP
identity register. Identity therefore belongs to the build/package trust
boundary, not a speculative MMIO probe.

## Upstream Contract Boundary

The accepted PL baseline is Cosmos+ OpenSSD commit
`78601486bb5581e40628ec7e841dea8e97eff034`.

| Owner | Upstream sources | Bound contract |
|---|---|---|
| NFC | `nsc_driver.{h,c}`, `ftl_config.h`, `request_schedule.c`, Tiger4 `Dispatcher.v`, `Decoder.v`, completion/ECC RTL, 8Ch8Way v3.0.0 HDF/HWH | 8 channels at `0x43C00000..0x43C7FFFF`; 8 ways; uProgROM commands; V2F DMA and ECC layout |
| PCIe | `nvme/host_lld.h`, `s_axi_reg.v`, PCIe `.xci`, AMD PG054 | CPU aperture `0x83C00000/0x10000`; endpoint/link/function/NVMe/queue state; `10EE:7028`, class `010802`, 8 KiB BAR0, MSI |
| Zynq PS | AMD UG585 and Cortex-A9/GIC/PL310 architecture | SLCR/DEVCFG, CPU1 `0xFFFFFFF0`, SCU, GICv1, MMU/cache, BootROM/FSBL |

The trusted upstream `OpenSSD2.bit` hash currently recorded by the NFC contract
is `66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2`.
Any rebuilt HDF/bitstream is a new contract until its generated address map and
RTL/software compatibility are reviewed.

## Layers and Ownership

1. **Entry/fault layer - `cosmos_start.S`:** vector table, VBAR, CPU-private
   temporary stacks, reset split, prefetch/data abort capture, CPU1 park/release.
2. **ABI layer - `cosmos_runtime.c`:** deterministic memory/string and ARM EABI
   primitives only; allocator and full Simple runtime remain outside this HAL.
3. **Memory/coherency layer - `cosmos_mmu_cache.c`:** shared translation table,
   SCU/`ACTLR.SMP`, per-core MMU/L1, CPU0-owned PL310.
4. **Interrupt/SMP layer - `cosmos_smp_gic.c`:** CPU0-owned GIC distributor,
   per-core GIC CPU interface, generation-tagged secondary mailbox.
5. **Handoff layer - `cosmos_fsbl.spl`:** Pure-Simple read-only validation of the state the
   FSBL must establish. It does not duplicate clock, DDR, reset, or PL loading.
6. **PL drivers - `cosmos_nfc.c`, `cosmos_pcie.c`:** exact upstream register
   contracts, bounded state machines, no generic discovery.
7. **Boot policy/integration - `cosmos_boot_policy.spl` with
   `cosmos_uart.c` bridge:** pure Simple owns UART enable-mask transitions,
   first-exception capture/message selection, stage and handoff admission,
   aggregate software readiness, QEMU/silicon terminal verdicts, IRQ enable,
   and storage-poll state transitions. C retains UART MMIO and bounded polling,
   volatile exception publication, assembly halt/WFI, status-string pointer
   rendering, HAL calls, and their side-effect sequencing.
8. **Artifact boundary - `build.shs`, `package_boot.shs`:** strict ELF build,
   Bootgen partition order, input/output identity, manifest and hashes.

`cosmos_hal.h` is the public boundary. Register headers are lane-private
contracts. No PL driver may initialize PS clocks/resets, and no FSBL validator
may issue NAND or PCIe operations.

## Address and Memory Model

| Range | Type and owner |
|---|---|
| `0x00000000..0x03FFFFFF` | normal cached/shareable DDR for the current 64 MiB image window |
| Reserved NFC DMA interval | normal uncached/shareable, identity mapped, excluded from allocators; exact bounds must come from the bound platform manifest |
| `0x43C00000..0x43CFFFFF` section | device/XN; NFC channels occupy `0x43C00000..0x43C7FFFF` |
| `0x83C00000..0x83CFFFFF` section | device/XN; PCIe controller uses first `0x10000` |
| `0xE0000000` section | device/XN; Cadence UART |
| `0xF8000000` and `0xF8F00000` sections | device/XN; SLCR/DEVCFG and SCU/GIC/PL310 |
| high OCM section containing `0xFFFFFFF0` | normal uncached/shareable/XN data mapping; CPU1 BootROM vector is written before `SEV` |

The 1 MiB short-descriptor granularity means the mapped device section is
larger than each logical aperture. Profile binding and fault containment remain
mandatory; mapping alone is not permission to probe.

## Boot State Machine

```text
reset -> VBAR/stacks/UART -> runtime self-test
      -> MMU table + SCU + ACTLR.SMP + L1 + CPU0 PL310
      -> CPU0 GIC distributor/interface
      -> FSBL self-test + read-only handoff validation
      -> bound NFC init and bound PCIe snapshot
      -> CPU1 vector/SEV -> CPU1 MMU/coherency/GIC -> generation ACK
      -> mount NFC metadata -> recover FTL -> bind NVMe services
      -> profile verdict -> foreground dispatch + bounded background GC
```

Every arrow is conditional. Runtime, MMU/cache, or GIC failure suppresses all
dependent work. QEMU intentionally stops the hardware lanes at
`UNAVAILABLE`. Silicon requires all mandatory lanes to be `OK`.

The boot extraction slice contains 15 scalar exports and 38 named semantic
predicate sites. Its Simple execution mask has two outcomes per predicate, so
the owner denominator is 76 outcomes. The independent frozen C oracle lowers
to 34 compiler branch sites and therefore 68 LLVM branch edges. Those are two
different scoped measurements: 38/76 describes named production semantics;
34/68 describes compiler-instrumented oracle control flow. Neither is
whole-HAL or physical-board coverage.

## NFC Concurrency and Failure Model

NFC operations are synchronous and serialized per channel; independent
channels may progress concurrently. The command sequence writes parameters,
uses DSB, issues the uProgROM command, and polls a defined completion/status
location. Validation occurs before lock acquisition and MMIO. A timeout marks
the channel faulted and retains DMA ownership until reset because hardware may
still write. ECC decoding separates CRC, spare, page validity, worst chunk
error count, and refresh recommendation (`>20`).

## PCIe Snapshot Model

The endpoint is host-configured. Firmware therefore observes rather than
fabricates Bus Master, MSI, link, NVMe, and queue state. It samples link,
function, NVMe, and admin state and confirms link remained up before accepting
the snapshot. Undefined bits, partial queue validity, MSI-X, impossible
ready/enable combinations, and excessive MME are errors. Link/configuration not
yet available is not production success.

The pinned HWH binds `NVMeHostController_0/dev_irq_assert` to GIC ID `61`,
active-high level. CPU0 targeting is local policy, not artifact proof. The IRQ
acknowledges configuration/link/error state only; command arrival is polled
from the controller command FIFO. PCIe transport covers command FIFO metadata,
16-DW SRAM fetch, three-word completion publication, and direct/AUTO host-DMA
descriptor ordering.

## Profile and Artifact Trust

Profiles are:

- `qemu`: never accesses NFC/PCIe/FSBL silicon registers; permits hardware lanes
  to be `UNAVAILABLE`; emits only software PASS plus silicon PENDING.
- `silicon-unbound`: compiles the silicon code but has no authority to access PL
  apertures; useful only for H0 link checks.
- `silicon-bound`: must be generated from an immutable manifest tying the exact
  bitstream hash to NFC/PCIe tokens and the reserved uncached DMA interval.
  The build receipt covers every compiled source/header plus compiler/linker
  identities. Package manifest v3 additionally requires a clean repository
  revision, board serial/revision, boot mode, Bootgen identity, contract token,
  DMA/toggle addresses, and hashes for every input/output. Only a verified
  matching physical package can enter board acceptance.

The QEMU and unbound profiles remain software-only. The bound profile is still
not production acceptance: the exact approved bitstream, real Bootgen output,
and identified-board evidence must match the receipt before flashing.

## Status and Fault Contract

`COSMOS_OK`, `COSMOS_UNAVAILABLE`, `COSMOS_INVALID`, `COSMOS_TIMEOUT`, and
`COSMOS_HW_ERROR` are exhaustive operator-visible results. `UNAVAILABLE` means
the required precondition/device is absent, not success. `INVALID` means a
software/input contract failure. `TIMEOUT` means bounded progress expired.
`HW_ERROR` means observed state contradicted the bound contract.

Prefetch/data abort is terminal. The handler records kind, syndrome, address,
and PC on a dedicated stack, emits a bounded UART marker if safe, disables
interrupts, and parks. It may not resume a storage operation.

## Verification Architecture

Production uses three independent evidence layers:

1. H0 strict build/artifact checks.
2. H1 executable QEMU, pure-logic, package, and host mock-MMIO tests.
3. H2 retained board evidence.

The H1 entry points are runtime ABI, MMIO, ARM abort, PCIe, NVMe IO, PCIe
bridge, NVMe admin, and SMP/cache runners, plus the package self-test and QEMU
boot. Receipts predating the pure-Simple FSBL migration remain historical
C-only evidence. The migrated MMIO runner, package self-test, QEMU build, and
silicon build require a current provenance-qualified Stage-4 compiler and must
be rerun before they are current H1 evidence.
Static source guards are supplementary, not behavioral proof. Synthetic Bootgen
output proves rejection logic, not BootROM compatibility. No H0/H1 result may
satisfy an H2 requirement.

## Operational Scope Boundary

This HAL has bounded IO and admin callback cores plus a PCIe bridge. The IO core
preserves queue/slot/sequence/CID, validates DMA spans, encodes SCT/SC/DNR, and
does not retry an ambiguous completion. The bridge decodes DW0/DW1/DW6..DW12
and delegates direct PRP2 and PRP-list walking to controller AUTO DMA. Admin covers Identify/SMART, queue
lifecycle, features, Abort, and AER. A crash-consistent FTL metadata core now
provides PPA geometry, append-before-map journaling, dual checkpoints,
fail-closed replay, retirement guards, a 10% reserve, and bounded
relocate-before-erase GC. The NFC backend adds explicit little-endian page
formats, page tags, rotating checkpoints, journal reclamation, and
program-once/erase-before-reuse behavior. The media adapter stages four 4 KiB
LBAs per 16 KiB NAND page and implements read-modify-write, Write Zeroes, DSM
discard, FUA flush, and LR retry policy. The single-owner dispatcher runs from
the UART foreground after silicon mounts and recovers existing metadata; it
never auto-formats NAND. A corrected-ECC read returns data first, then asks the
FTL to transactionally relocate the still-current PPA; failed relocation does
not replace the old mapping. Physical correction margin and board proof remain
pending.

## Current Production Gate

H1 runtime, PCIe, IO, corrected bridge/admin, and MMU small-page W^X contracts
passed in scoped runs. The earlier MMIO, QEMU/silicon, and package passes used
the former C-owned FSBL and are retained only as historical evidence; migrated
mixed-object reruns are pending. Corrective bridge/admin
evidence covers Abort/queue/SMART fields, zero-write-only completion retry,
post-start non-retry, and PRP edges. Official Bootgen v2026.1, the pinned
upstream HDF/`OpenSSD2.bit`, vendor-generated FSBL, and the pre-migration
silicon package have retained host hashes. Their Manifest v3 provenance and
standalone artifact checks are historical; the migrated package rerun and
identified-board execution remain pending.

The unchanged-tree bootstrap rebuilt authority and passed Stage 2/3 sanity.
Stage 4 cleared the prior parser/HIR crashes, then failed on unresolved names
from partial/header-only import facades at 5,492,252 KiB peak RSS. No runner
was produced or deployed. The active compiler defect is tracked in
`doc/08_tracking/bug/bootstrap_stage4_hir_import_crash_2026-07-27.md`.
No current pure-Simple runner exists for final SSpec/doc generation.
Production status is **BLOCKED/FAIL**. Fresh SSpec/docgen and H2 board proof
remain required.

## Pure-Simple PCIe/NVMe Queue Policy Slice (2026-08-19)

`cosmos_nvme_pcie_policy.spl` is now the sole production owner of completion
status validation/encoding and I/O SQ/CQ descriptor validation and control-word
derivation. `cosmos_nvme_pcie_policy_bridge.c` retains only the unavoidable C
pointer ABI: it rejects null output pointers, delegates every decision, and
publishes the two 32-bit words. `cosmos_pcie.c` continues to own volatile MMIO,
barriers, FIFO commit ordering, IRQ service, and transport quiescence; it no
longer owns this queue policy.

The existing public firmware symbols are unchanged. The clean build emits a
separate Cortex-A9 pure-Simple object, admits exactly six policy exports with
an empty undefined-symbol closure, links the C bridge, and binds all inputs in
the firmware receipt. Host evidence compares exhaustive bounded vectors to an
independent frozen C oracle and reports LLVM-instrumented C bridge branches
plus named Simple production-predicate outcomes. This evidence is scoped to
the migrated slice and does not represent whole-HAL, QEMU, or board coverage.

## NFC ECC Pure-Policy Boundary (2026-08-19)

`cosmos_nfc_ecc.spl` now owns Tiger4NSC CRC/spare/page validity, worst-chunk
extraction, the strict `>20` refresh threshold, and `OK`/`HW_ERROR` mapping.
`cosmos_nfc_ecc_bridge.c` is limited to two volatile DMA-word acquisitions,
null-boundary validation, and marshalling the unchanged
`cosmos_nfc_decode_ecc` C struct ABI. The scalar Simple object has six explicit
C exports and must have an empty undefined-symbol closure; production and every
focused `cosmos_nfc.c` link must include both the object and acquisition bridge.

Host evidence is deliberately scoped to exhaustive legacy-C oracle parity,
compiler-instrumented acquisition-bridge branches, and owner-derived Simple
policy decisions. It is not NAND media, ECC correction-margin, DMA-coherency,
or physical-board evidence.

## Residual Freestanding Runtime Boundary (2026-08-20)

`cosmos_runtime_residual.spl` owns the deterministic traversal, overlap,
comparison, terminator, scan-bound, and padding decisions for `memmove`,
`memcmp`, `strlen`, `strcmp`, `strncmp`, and `strncpy`. `cosmos_runtime.c`
retains the public libc, `rt_*`, and ARM EABI names as ABI forwarding shims.
The previously extracted `cosmos_runtime_core.spl` remains the unchanged owner
of copy/fill/unsigned-division and division-by-zero policy; weak div0 hooks,
runtime initialization, traps, and the boot self-test remain in C.

The residual object is allocation-free, exports only six internal operations
and four coverage queries, has an empty undefined closure, and is admitted as
Cortex-A9 soft-float ELF32 before production linking. This slice has 27 named
Simple decisions/54 outcomes. Its frozen six-function C oracle has exactly 68
LLVM branch edges and 40 pinned evidence rows. Those source/static results do
not imply executable C-vs-Simple parity: that claim fails closed without an
admitted provenance-qualified Stage-4 compiler.
