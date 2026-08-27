# Cosmos+ OpenSSD Production HAL Detail Design

## Shared Contract

`cosmos_hal.h` owns five statuses, platform bases, `COSMOS_POLL_LIMIT`,
volatile 32-bit MMIO, and DSB/ISB. Public lane entry points are:

- NFC: `cosmos_nfc_init`, `cosmos_nfc_selftest`,
  `cosmos_nfc_{read_page,program_page,erase_block,status,decode_ecc}`.
- PCIe: `cosmos_pcie_init`, `cosmos_pcie_selftest`.
- Runtime: `cosmos_runtime_init`, `cosmos_runtime_selftest`.
- SMP/GIC: `cosmos_cpu_id`, `cosmos_gic_init_{primary,secondary}`,
  `cosmos_smp_release_secondary`, `cosmos_smp_selftest`.
- Memory: `cosmos_mmu_cache_init`, `cosmos_mmu_cache_selftest`.
- Handoff: `cosmos_fsbl_validate_handoff`, `cosmos_fsbl_selftest`.
- NVMe callback service: `cosmos_nvme_service_init`,
  `cosmos_nvme_service_poll`.
- PCIe bridge: `cosmos_nvme_pcie_service_init`.
- Admin callback core: `cosmos_nvme_admin_init`, `cosmos_nvme_admin_poll`.

All initialization is idempotent or fail-sticky where hardware ownership makes
retry unsafe. Callers propagate the exact status; only the terminal coordinator
decides whether a profile may pass.

The 24 scalar SMP/GIC helpers are C-ABI exports from
`cosmos_smp_gic_policy.spl`. They own mailbox request validation, generation
wrap, GIC word/offset/mask/value derivation, PCIe IRQ range checks, EOIR policy,
and unhandled-IRQ quiesce selection. `cosmos_smp_gic.c` retains only contract
forwarders plus CPU/MMIO/barrier/assembly, interrupt dispatch, and mailbox
publication. The frozen pre-migration oracle has 17 compiler decisions and 34
branch outcomes; source gates pin that denominator separately from board proof.

The two Handoff symbols are C-ABI exports from `cosmos_fsbl.spl`. Its pure
`cosmos_fsbl_handoff_status` function owns all required-bit and forbidden-reset
decisions, while `cosmos_fsbl.c` exports only
`cosmos_fsbl_bridge_is_qemu` and `cosmos_fsbl_bridge_read32`. Internal Simple
outcome accessors are not HAL APIs; only `COSMOS_FSBL_COVERAGE_TEST` C builds
expose reset/snapshot wrappers for them. Host and ARM integration must link the
emitted Simple object; compiling the bridge alone is not evidence for the
handoff behavior.
The Simple and C objects both use the named Cortex-A9 soft-float
`armv7-unknown-none-eabi` contract. Object admission checks ELF32/ARM/REL,
ARMv7/Cortex-A9-compatible attributes, exactly the two production FSBL exports,
exactly the two undefined acquisition bridges, and absence of runtime or entry
definitions before final linking.

The 15 boot/UART scalar functions are C-ABI exports from
`cosmos_boot_policy.spl` through `cosmos_boot_policy.h`. This extraction owns
UART enable-mask transitions, first exception-capture/message selection,
status normalization, stage/software/handoff/storage/secondary admission,
platform terminal verdicts, IRQ admission, and storage-poll transitions.
`cosmos_uart.c` keeps direct UART MMIO and timeout polling, volatile exception
writes, assembly halt/WFI, status-string pointer selection, HAL calls, and the
imperative ordering needed to perform those effects.

Coverage uses deliberately separate denominators. The Simple owner has 38
named semantic predicate sites and records both results for 76 outcomes. The
independent pre-migration C oracle compiles to 34 LLVM branch sites and 68
branch edges. The 279-row parity matrix compares C and Simple results; it does
not turn the 34 compiler sites into 38 semantic predicates. Focused and
production object admission require exactly the 21 declared globals (15
policy plus six coverage exports), no entry/runtime definitions, an empty
undefined-symbol closure, and no hard-float/VFP attributes. The admitted
receipt also freezes the exact silicon profile header.

## NFC Register Contract

The register file is repeated at a `0x10000` stride for channels 0..7.

| Offset | Register | Use |
|---|---|---|
| `0x00` | command select | uProgROM entry: reset 1, set-features 6, read trigger 13, read transfer 18, program 28, erase 37, status 41 |
| `0x04` | row address | 24-bit NAND row |
| `0x08` | user data | toggle-mode feature payload |
| `0x0C` / `0x10` | data/spare address | identity-mapped uncached DMA |
| `0x14` / `0x18` | error/completion address | 11 ECC words and one completion word |
| `0x1C` | way selection | target 0..7 |
| `0x20` / `0x24` / `0x2C` | channel busy / ready-busy / controller idle | bounded progress checks |

Geometry is 16,384 data bytes, 256 spare bytes, 256 rows/block, LUN0 rows
`0x000000..0x1057FF`, and LUN1 rows `0x200000..0x3057FF`. Erase accepts only
the first row of a block. The two row ranges deliberately reject the gap.

### NFC Binding and DMA

`COSMOS_NFC_PACKAGE_VERIFIED_OPENSSD2_8C8W_3_0_0` binds registers only after
the trusted package step verifies upstream `OpenSSD2.bit` SHA-256
`66e863b2ff2c0190928e3e71aeba9725551584cffc32854928946b1720cbf5c2`.
IO additionally requires `COSMOS_NFC_DMA_IDENTITY_BASE`,
`COSMOS_NFC_DMA_IDENTITY_END`, and
`COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS`.

Every DMA range must be 4-byte aligned, fully contained, and non-overlapping.
The MMU/linker/platform manifest must reserve the region as CPU/PL
identity-mapped uncached memory. These values have no safe defaults.

### NFC Operation Sequences

- `init`: verify local contract -> verify binding and `PCFG_DONE` -> validate
  toggle payload -> for each channel and way reset, wait idle/ready, write
  upstream feature payload, issue set-features, wait idle/ready -> publish
  initialized.
- `read_page`: validate -> lock channel -> trigger read -> poll NAND status ->
  clear completion/ECC -> program DMA addresses -> transfer -> wait
  `0xA5000001` -> wait idle -> decode ECC -> unlock.
- `program_page`: validate -> lock -> program row/data/spare -> issue program ->
  poll NAND status -> unlock.
- `erase_block`: validate block-aligned row -> lock -> issue erase -> poll NAND
  status -> unlock.
- `status`: repeatedly issue status only when channel/way are ready; decode DONE,
  complete mask `0x60`, and fail mask `0x03`.

Any operation timeout atomically quarantines the channel. DMA remains
controller-owned until reset. ECC success requires CRC valid, spare valid, and
page-valid word; worst chunk errors over 20 request refresh.

## PCIe Register Contract

The bound upstream controller occupies `0x83C00000..0x83C0FFFF`.

| Offset | Register | Required interpretation |
|---|---|---|
| `0x0100` | status | LTSSM bits `[5:0]`, link-up bit 8; L0 is `0x16` |
| `0x0104` | function | Bus Master, MSI, MSI-X, INTx, MME |
| `0x0200` | NVMe status | controller enable/shutdown and ready/shutdown state |
| `0x021C` | admin queues | CQ valid, SQ valid, CQ IRQ enable |
| `0x0220` / `0x0260` | IO SQ/CQ windows | board queue testing; readiness probe does not mutate them |

The synthesized endpoint is vendor/device `10EE:7028`, class `010802`, BAR0
mask `FFFFE000` (8 KiB). `COSMOS_PCIE_BITSTREAM_CONTRACT` must equal
`COSMOS_PCIE_CONTRACT_8CH8WAY_V300`; another value fails compilation and no
value leaves the device unavailable.

The readiness loop first requires `PCFG_DONE`, then polls link-up, reads
function/NVMe/admin, and rechecks link before evaluating the snapshot. Unknown
bits, MSI-X, MME > 3, half-valid admin queues, IRQ without CQ, ready without
enabled/valid queues, and state while disabled are errors. Link, Bus Master, or
MSI not yet configured is unavailable until the bounded poll expires.

## Runtime

The runtime implements byte-correct `memcpy`, overlap-safe `memmove`, `memset`,
comparison/string primitives, their `rt_*` aliases, ARM EABI memory helpers,
signed/unsigned divide and packed divide/remainder helpers, weak
`__aeabi_idiv0`, and trapping unwind personalities. It intentionally provides
no allocator, environment, process, file, or host libc service.

Self-test covers overlapping move, string termination, `UINT_MAX/UINT_MAX`,
`UINT_MAX/2`, signed minimum/maximum division, signed minimum divided by `-1`
using the ARM wrap convention, and divide-by-zero hook behavior.

## MMU, Cache, SMP, and GIC

CPU0 builds one 4096-entry/16 KiB first-level table. MMU initialization:

1. Validate descriptor and cache operand constants.
2. CPU0 invalidates SCU state; each core enables SCU and `ACTLR.SMP`.
3. Clean/invalidate L1 by CLIDR/CCSIDR set/way using `clz(ways - 1)`.
4. CPU0 performs bounded PL310 all-way maintenance and enables L2.
5. Install TTBCR/TTBR0/DACR, invalidate TLB/instruction side, then enable
   SCTLR.M/C/I.

QEMU skips PL310 register access because its Zynq model does not expose a
usable block; that is a model limitation, not board evidence.

CPU0 disables and initializes the GIC distributor, clears enables/pending/active
state, assigns priorities/targets, enables it, then initializes its CPU
interface. CPU1 initializes only its private CPU interface.

CPU1 BootROM waits for an event and reads `0xFFFFFFF0`. CPU0 publishes entry,
stack, and mailbox, cleans them, writes `cosmos_secondary_start` to that
address, DSBs, and SEVs. After CPU1 reports READY, CPU0 publishes a nonzero
generation and RELEASED. CPU1 installs its real stack, initializes
MMU/coherency and GIC, then ACKs the same generation. Timeout publishes
CANCELLED and parks CPU1.

## FSBL, Exceptions, and Boot Coordinator

Reset installs `_start` as VBAR before any optional PL access. Prefetch/data
abort captures IFSR/IFAR or DFSR/DFAR and fault PC on a dedicated abort stack,
then enters `cosmos_exception_halt`.

The FSBL validator is read-only. It requires:

- SLCR lock bit set;
- ARM clock active mask at SLCR `0x120`;
- DDR clock active mask at SLCR `0x124`;
- primary PS reset clear at `0x200`;
- CPU0 reset/clock-stop clear at `0x244`;
- `DEVCFG.INT_STS.PCFG_DONE` at `0xF800700C`.

The coordinator initializes UART, runtime, MMU/cache, and primary GIC in order,
while `cosmos_boot_policy.spl` decides every subsequent admission and terminal
state. It does not run dependent lanes after foundational failure. QEMU then
expects FSBL/NFC/PCIe/CPU1 unavailable. A bound board profile validates FSBL
and PL, then releases CPU1; every mandatory status must be `OK` for silicon
PASS. UART TX polling is bounded in C; pure Simple permanently removes an
unresponsive UART from the enabled mask.

## Package and Manifest

`package_boot.shs` requires `--fsbl`, `--bitstream`, `--elf`, `--board-serial`,
`--board-revision`, and `--boot-mode sd|qspi`, with optional `--output`. It
rejects dirty or unidentified source trees and validates files, canonical path/inode aliases, ARM ELF identity,
nonzero entry, `PT_LOAD`, silicon marker, Xilinx sync word, Bootgen result size,
Zynq width/signature words, and `bootgen -read` metadata. It emits partitions
in FSBL -> bitstream -> firmware order and atomically publishes `boot.bin` plus
`boot.bin.manifest`.

Manifest v3 records the clean repository revision, board serial/revision, boot
mode, silicon profile/contract, DMA/toggle addresses, compiler/linker/Bootgen
versions and executable hashes, canonical paths, and SHA-256 for FSBL,
bitstream, firmware receipt/ELF, metadata, and boot output. The build receipt
binds every compiled source/header and the exact compiler/linker identities.
`--verify-manifest` revalidates required unique fields and current artifact
hashes. Historical pre-migration receipts cover the synthetic packager
rejection logic and a Bootgen v2026.1 invocation. The migrated mixed-object
package rerun, physical BootROM, and board runs remain required for production
evidence.

## Host Mock-MMIO Design

Under the test define, the native MMIO/event backends record scripted reads,
writes, barriers, and terminal events while production retains direct inline
MMIO. The H1 runner set is:

- `sh test/02_integration/os/cosmos/run_cosmos_hal_mmio_test.shs`
- `sh test/02_integration/os/cosmos/run_cosmos_abort_contract_test.shs`
- `sh test/02_integration/os/cosmos/run_cosmos_pcie_contract_test.shs`
- `sh test/02_integration/os/cosmos/run_cosmos_nvme_firmware_contract_test.shs`
- `sh test/02_integration/os/cosmos/run_cosmos_smp_cache_contract_test.shs`

The non-FSBL runners retain their earlier scoped evidence. The modified MMIO
runner links the pure-Simple object, verifies its production export/bridge
symbol closure, checks all FSBL masks and ordered reads, and checks the QEMU
no-MMIO composition. The separate coverage gate pins the emitted policy object,
12 production decision locations, and 24 runtime outcomes while retaining the
C bridge LLVM result as its own 2/2 slice. Both are pending execution with an
admitted Stage-4 compiler; the older C-only MMIO receipt is historical. Once
rerun, the set covers:

- every FSBL predicate and no-PL-read-on-failure;
- NFC valid/invalid geometry and DMA, all completion/error/timeout paths,
  channel locking/quarantine, and ECC thresholds;
- PCIe stable/unstable snapshots, invalid bits, link/configuration progression,
  and timeout;
- CPU1 vector/barrier/event/mailbox generation and ACK/cancel ordering;
- descriptor values, SCU/ACTLR ordering, set/way operands, PL310 completion and
  timeout;
- bounded UART and startup fail-closed ordering;
- actual prefetch/data-abort vector entry, syndrome/address/PC capture, and
  terminal non-resumption under bounded QEMU injection.

The harnesses execute behavior; grep-only source guards are supplementary.

## NVMe Integration Boundary

The IO callback core preserves queue/slot/sequence/CID identity, checks exact
DMA spans before media callbacks, returns SCT/SC/DNR status, and
retries only an explicitly not-committed completion. The PCIe bridge decodes
DW0/DW1/DW6..DW12 and translates the controller command/completion transport;
controller AUTO DMA walks direct PRP2 and PRP-list transfers. The bridge
requires caller-provided read/program/flush/write-zeroes/deallocate callbacks.
The bounded admin
core supports Identify/SMART, queue lifecycle, Number-of-Queues features,
Abort, AER, and explicit unsupported Format/Firmware rejection.

Corrected bridge/admin host/ARM runners pass Abort result-bit,
Number-of-Queues NSID/max, CQ IEN/IV, SQ QPRIO, SMART NSID/RAE, PRP edge,
zero-write retry-boundary, and post-start non-retry checks. The NFC backend
serializes metadata explicitly, rotates dual checkpoints, reclaims the journal,
tags data pages, and preserves program-once semantics. The media adapter maps
4 KiB NVMe commands onto 16 KiB NAND staging with read-modify-write, zeroes,
discard, FUA, and LR behavior. `cosmos_storage` mounts and recovers the FTL,
binds IO/admin/dispatch services, and runs foreground polling only after NFC
and PCIe are ready. QEMU returns `UNAVAILABLE`; silicon never auto-formats
missing metadata. Corrected-ECC reads preserve the delivered host data and then
relocate the page through the existing append-before-map transaction, provided
the source PPA is still current. Relocation failure leaves the old mapping
authoritative and fails the command before completion. Physical ECC margin and
queue behavior remain H2 work. PCIe
IRQ 61 is level-high configuration/link/error handling, not command arrival.
W^X is implemented with firmware small pages. H1 proves the vector/handler
contract; physical-board abort behavior remains H2.
Focused host/ARM ECC relocation, destination reread, stale-source rejection,
failure preservation, remount/replay, and relocatable-link checks pass. Final
SSpec/doc generation remains blocked. The unchanged-tree strict build passed
Stage 2/3 sanity, cleared the prior parser/HIR crashes, and failed Stage 4 on
unresolved names from partial/header-only import facades. Official Bootgen
v2026.1, the pinned bitstream, vendor-generated FSBL, and real package are
available with retained historical hashes. The migrated Manifest v3 software
provenance/tamper rerun and board evidence remain pending.

## Error and Evidence Rules

No function may translate `UNAVAILABLE`, `INVALID`, `TIMEOUT`, or `HW_ERROR`
into `OK`. No board procedure may reuse QEMU output as evidence. Each run stores
command, exit code, stdout/stderr, artifact hashes, tool versions, and for H2
the board serial/revision and fixture identity.

## PCIe/NVMe Queue Policy Migration Detail

The pure-Simple owner validates SCT/SC/DNR, queue IDs 1 through 8,
enabled/disabled descriptor shape, 1 through 256 entries, 4 KiB alignment, the
36-bit host-address ceiling, SQ-to-CQ binding, and CQ IRQ/vector fields. Only
after validation does it derive the exact RTL control word. Disabled
descriptors must be completely zeroed.

The C bridge keeps the exact legacy symbols
`cosmos_pcie_nvme_status_word`, `cosmos_pcie_nvme_io_sq_words`, and
`cosmos_pcie_nvme_io_cq_words`. Its only policy-adjacent work is null-output
admission and scalar publication. Configuration remains in `cosmos_pcie.c`
because final register writes and barriers are volatile hardware operations.
The bridge must not duplicate masks, range checks, or descriptor encoding.

`check-cosmos-nvme-pcie-policy.shs` compares the Simple owner with a frozen C
oracle over the bounded cross-product, measures the C bridge with LLVM source
coverage, runs the Simple decision manifest, binds source hashes in a scoped
receipt, and labels physical-board evidence separately unavailable.

## NFC ECC Policy Migration Detail (2026-08-19)

The public signature and `struct cosmos_nfc_ecc` layout are unchanged. The C
bridge acquires `error_info[0]` and `[1]` exactly once, then calls pure scalar
Simple exports for the five fields and terminal status. This prevents a torn
double-read while leaving MMIO/DMA acquisition in C. The policy object cannot
import runtime, allocation, MMIO, or process symbols.

The parity matrix crosses CRC validity, spare validity, all 256 encoded error
counts, three page-validity words, and two unrelated-bit patterns: 6,144 cases,
plus each null boundary. The scoped evidence gate rejects a zero branch or
decision denominator and records `board_evidence=separate-not-included`.
The 2026-08-19 source-bound bridge receipt records 4/4 compiler-instrumented
branch outcomes. Simple decision execution and C-oracle parity remain blocked,
not inferred, because no admitted Stage-4 compiler is installed.

## Residual Runtime Extraction Detail (2026-08-20)

The six public C functions remain stable ABI entry points and immediately
delegate to `cosmos_runtime_residual_*`. The pure owner preserves legacy null
ordering, byte-difference return values, overlap-safe reverse copying, the
1,000,000-byte scan bound, early NUL termination, and zero padding. It neither
imports nor defines libc, `rt_*`, EABI, entry-point, allocation, MMIO, or
process symbols.

`check-cosmos-runtime-residual-policy.shs --source-only` compiles both host and
ARM C shims, pins their eleven-symbol Simple dependency closure, executes the
independent frozen C oracle, and requires all 68 LLVM branch edges. The default
mode additionally emits strict host/ARM Simple objects and runs 40-row
C-vs-Simple parity with all 54 named outcomes; it exits BLOCKED before those
claims when Stage-4 provenance is unavailable.
