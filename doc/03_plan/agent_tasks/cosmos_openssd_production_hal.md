# Cosmos+ OpenSSD Production HAL Agent Tasks

## Frozen Interfaces

All lanes use `enum cosmos_status` from `cosmos_hal.h`. No lane may invent a
second MMIO/status abstraction, access another lane's registers, weaken
profile binding, turn a timeout into success, or claim board evidence from
QEMU. Shared startup order is runtime -> MMU/coherency -> primary GIC -> FSBL
handoff -> NFC/PCIe -> CPU1 release.
The HAL lane now has host/ARM IO callback, PCIe bridge, and admin contract
runners. Their media callbacks remain mocked/caller-supplied; they are not an
FTL, boot integration, or board proof.

## Lane Ownership and Acceptance

| Lane | Primary files | Required delivery | Current state |
|---|---|---|---|
| Profile/binding | `build.shs`, NFC/PCIe register headers, `package_boot.shs` | One verified bitstream identity drives compile tokens, DMA reservation, receipt, and manifest; mismatch fails closed. | H0/H1 receipt and rejection checks implemented; pinned host artifact hashes retained, physical board provenance pending. |
| NFC | `cosmos_nfc.c`, `cosmos_nfc_regs.h` | Pinned 8Ch8Way v3.0.0 registers; 8x8 init; bounded status/read/program/erase; ECC decode; DMA validation; timeout quarantine. | H1 host MMIO coverage present; board NAND evidence pending. |
| PCIe | `cosmos_pcie.c`, `cosmos_pcie_regs.h` | Pinned endpoint aperture/IDs/BAR; IRQ 61 level-high handling; command/completion FIFO and direct/AUTO host-DMA transport. | H1 runner passed; CPU0 target is local policy and board IRQ/DMA evidence pending. |
| Runtime | `cosmos_runtime.c` | Freestanding memory/string/EABI/division support with edge self-test and no unresolved symbols. | Runtime H1 runner passed; final pure-Simple SSpec remains blocked. |
| SMP/GIC | `cosmos_start.S`, `cosmos_smp_gic.c` | VBAR/stacks; GICv1 ownership; HDF-bound level-high IRQ 61 route; Zynq CPU1 vector/SEV protocol; generation ACK after secondary MMU/GIC. | H1 IRQ/SMP contract present; CPU0 target is policy and board delivery evidence remains pending. |
| MMU/cache | `cosmos_mmu_cache.c` | W^X firmware pages; XN DMA/MMIO/RW state; SCU/`ACTLR.SMP`; set/way maintenance; per-core MMU/L1; CPU0 PL310 bounded maintenance. | H1 W^X/SMP/cache contract present; live abort and board coherency stress pending. |
| FSBL/abort | `cosmos_start.S`, `cosmos_fsbl.c`, `cosmos_uart.c` | Abort containment; read-only SLCR/reset/clock/`PCFG_DONE` validation; no dependent startup after foundational failure. | H1 fail-closed and bounded QEMU abort injection pass; live-board abort and BootROM evidence pending. |
| Packaging | `package_boot.shs` | Validate explicit artifacts, Bootgen metadata, aliases, hashes, silicon identity, and publish manifest atomically. | Self-test and official Bootgen v2026.1 package pass; physical BootROM/board evidence pending. |
| NVMe bridge/admin | `cosmos_nvme_pcie_adapter.*`, `cosmos_nvme_admin.*` | Decode controller commands, preserve completion identity/publication semantics, and serve bounded admin callbacks. | Corrected host/ARM runners pass Abort/queue/SMART fields, retry boundaries, and PRP edges; FTL/UART polling binding is implemented and ARM-compiled, with final SSpec and board service pending. |
| Host tests | Cosmos SSpec plus native runners | Execute completion, malformed state, timeout, ordering, and callback-service paths without board MMIO. | H1 runners passed: runtime, MMIO, PCIe, NVMe IO, bridge, admin, SMP/cache; final SSpec blocked on bootstrap. |
| Board tests | Guide procedures and retained evidence bundle | BT-001..BT-006 on identified Cosmos+ hardware. | **Pending:** no board success claimed. |

## Parallel Execution Plan

Agents run only within one wave and one exclusive write set. A later wave may
start when its listed dependencies are accepted by the merge owner; it does
not wait for unrelated lanes. Read-only reviewers may run concurrently with
any wave.

### Wave 0 - Interface Freeze

The merge owner records the exact signatures already present in the tree
before implementation sidecars start. Current shared names are:

- `cosmos_pcie_nvme_fetch_command`
- `cosmos_pcie_nvme_post_completion`
- `cosmos_nvme_service_init`
- `cosmos_nvme_service_poll`
- `cosmos_nfc_read_page`
- `cosmos_nfc_program_page`
- `cosmos_nfc_erase_block`

New PRP-DMA, admin, and FTL signatures are frozen in this document by the
merge owner before Waves 2A-2C start. Sidecars must not independently add
competing queue, DMA, FTL, status, or MMIO abstractions.

### Wave 1 - Independent Foundations

| ID | Agent lane | Exclusive write set | Delivery and acceptance | State |
|---|---|---|---|---|
| W1-A | PCIe command transport | `cosmos_pcie.c`, `cosmos_pcie_regs.h`, PCIe contract C/runner | Pinned command FIFO + 16-DW SRAM fetch, completion commit, IRQ 61, and direct/AUTO DMA; runner and ARM silicon build pass. | Complete |
| W1-B | Runtime ABI evidence | New runtime contract C/runner only | Host checks for overlap-safe `memmove`, memory/string ABI, signed/unsigned divide/mod and divide-by-zero hooks. | Complete |
| W1-C | Bootstrap resource fix | Compiler driver/runtime files selected after profiling; existing Stage-4 memory bug doc and one focused regression | Root-fix Stage-4 retention or allocation growth. One bounded resource smoke must produce the full CLI below the agreed RSS ceiling. Never repeat the full bootstrap more than the repository iteration cap. | Unassigned, blocking H0 |
| W1-D | Abort injection | New abort contract test and the minimum startup test seam; no production exception weakening | Inject data/prefetch aborts, prove IRQ/FIQ masking, captured fault state, no return to corrupt context, and deterministic halt. Host/ARM evidence only; live fault remains H2. | Complete for H1; H2 pending |

### Wave 2 - Data Path Components

Wave 2 starts after W1-A and the interface freeze. Its lanes remain separate:

| ID | Agent lane | Exclusive write set | Delivery and acceptance | Dependencies |
|---|---|---|---|---|
| W2-A | PCIe service adapter | New `cosmos_nvme_pcie_adapter.c/.h` and one adapter contract test | Decodes DW0/DW1/DW6..DW12, contiguous PRP floor/edges, identity, SCT/SC/DNR, zero-write retry, and post-start non-retry. Media remains caller-provided. | Complete: corrected host/ARM PASS |
| W2-B | Host PRP DMA | New host-DMA module and contract test; PCIe register header changes only through merge owner | Validate 64-bit PRP addresses, page splits, transfer length, direction, alignment, overflow, FIFO capacity, completion timeout, and profile-owned staging buffers. Unknown SGL forms fail with the correct NVMe status. | W1-A, frozen DMA API |
| W2-C | Persistent FTL/NFC adapter | New FTL/media module and tests; NFC driver remains owned by the NFC lane | Implement logical-to-physical mapping, journal/checkpoint recovery, bad-block retirement, ECC propagation, atomic write failure, durable flush, and bounded GC. Raw direct LBA-to-page mapping is not production acceptance. | Frozen FTL API, NFC H1 |
| W2-D | NVMe admin/controller | New admin/controller module and contract test | Identify/SMART NSID/RAE, queue IEN/IV/QPRIO, Number-of-Queues NSID/max, Abort result bits, AER, and unsupported Format/Firmware rejection. | Complete: corrected host/ARM PASS |

W2-A, W2-B, W2-C, and W2-D may run in parallel after their shared structures
are frozen. They exchange only fixed structs and callback signatures. Their
tests use injected adapters; no lane reads another lane's private state.

### Wave 3 - Integration

| ID | Agent lane | Exclusive write set | Delivery and acceptance | Dependencies |
|---|---|---|---|---|
| W3-A | Boot/service integration | `cosmos_uart.c`, `build.shs`, `cosmos_hal.h`; linker changes only if reviewed | Initialize the service only after runtime/MMU/GIC/FSBL/NFC/PCIe pass; poll commands outside the link/config IRQ; run bounded foreground work; fail fast on link/media loss; include every production object in both QEMU and silicon builds. | W2-A..W2-D |
| W3-B | End-to-end host model | New combined C runner | Exercise command fetch -> decode -> PRP DMA -> FTL/NFC mock -> committed completion, including malformed, timeout, reset, power-loss recovery, queue pressure, and exactly-once completion. | W3-A |
| W3-C | SSpec/manuals | Cosmos SSpec, generated manual, test plan, architecture/design/guide only | Add real adapter/end-to-end scenarios, retain callback-only scenarios as lower-level evidence, remove all false H2 traceability, regenerate docs using the deployed pure compiler. | W3-B, H0 compiler |

### Wave 4 - Verification and Hardware

The H0/H1 verifier and three board operators may work in parallel after Wave
3. The final reviewer starts only when their evidence is immutable.

| ID | Agent lane | Required evidence |
|---|---|---|
| W4-A | H0/H1 verifier | Run each exact command once; record command, runtime identity, stdout/stderr, exit code, elapsed time, max RSS, artifact hash, and requirement IDs. |
| W4-B | NAND board operator | Reserve destructive blocks; inventory 8 channels x 8 ways; program/read/erase/ECC/timeout/bad-block/power-loss evidence with raw logs. |
| W4-C | PCIe board operator | `lspci`, BAR, MSI, IRQ 61 link/config events, command polling, PRP DMA, reset/link recovery, `nvme` and bounded `fio` evidence. |
| W4-D | SMP/boot board operator | BootROM/FSBL cold/warm boot, CPU1 release, IAR/EOIR, W^X abort, shared-cache and PL-DMA coherency stress with serial logs and artifact hashes. |
| W4-E | Evidence assembler | Board identity, tool versions, boot mode, immutable binaries/bitstream/BOOT.BIN, hashes, timestamps, logs, and signed evidence index. |
| W4-F | Final reviewer | Independent highest-capability review of source plus H0/H1/H2 evidence; issue only `PASS`, `WARN`, or `FAIL` with file/line and evidence references. |

## Detailed Agent Guide

Every implementation sidecar receives this checklist with its lane-specific
write set:

1. Read `AGENTS.md`, this plan, the applicable architecture/design, and all
   callers of the functions it will change.
2. Confirm the worktree path and list its exclusive files before editing.
   Stop if another active lane owns one of them.
3. Cite the pinned upstream commit and exact register/spec source for hardware
   constants. Guessed offsets, IRQs, masks, timing, or success values are
   forbidden.
4. Reuse `enum cosmos_status`, MMIO helpers, barriers, profile constants, and
   existing bounded polling helpers. Do not add a second platform abstraction.
5. Validate every external address, length, count, queue ID, slot, channel,
   way, row, opcode, and state transition before MMIO or media access.
6. Treat timeout, torn state, link loss, ECC failure, ambiguous completion,
   and unsupported command as fail-closed. Never convert them to success.
7. Add one focused runnable contract test that fails before the change. Mocks
   reject unknown MMIO and count ordering/duplicate operations.
8. Compile host tests with `-Wall -Wextra -Werror`; compile changed firmware
   for `armv7-none-eabi` with freestanding flags. Run each acceptance check
   once.
9. Report files changed, exact commands/results, unresolved dependencies, and
   whether each result is H0, H1, or H2. Do not commit, rebase, or push.

Agents use fail-fast assertions in unfinished tests. Placeholder passes,
TODO-only bodies, broad catch-all mocks, sleeps, unbounded retries, test-only
production bypasses, and physical-board claims from QEMU are prohibited.

## Merge Handoff

The merge owner reviews each lane before exposing it to the next wave:

- API and ownership match the Wave 0 freeze.
- No unrelated dirty file is included.
- Host and ARM checks are reproducible and were run once.
- Hardware constants trace to the pinned profile.
- Status and publication semantics are exact and fail-closed.
- Documentation states exclusions and board-only gaps.

Rejected lanes return to their original owner; the merge owner does not patch
around a broken private contract in another lane.

## Exact Verification Commands

```sh
sh -n test/02_integration/os/cosmos/run_cosmos_pcie_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_hal_mmio_test.shs
sh test/02_integration/os/cosmos/run_cosmos_pcie_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_firmware_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_runtime_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_pcie_adapter_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_nvme_admin_contract_test.shs
sh test/02_integration/os/cosmos/run_cosmos_smp_cache_contract_test.shs
COSMOS_BUILD_MODE=qemu sh src/os/kernel/arch/arm32/cosmos/build.shs --run
COSMOS_BUILD_MODE=silicon COSMOS_SILICON_PROFILE=openssd2-8ch8way-v3.0.0 \
  sh src/os/kernel/arch/arm32/cosmos/build.shs
sh src/os/kernel/arch/arm32/cosmos/package_boot.shs --self-test
bin/release/simple test \
  test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl \
  --mode=interpreter
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
test "$(find doc/06_spec -name '*_spec.spl' | wc -l)" -eq 0
```

Do not run the final SSpec with a stale compiler/runtime. Current scoped results
include runtime, PCIe, NVMe IO, PCIe bridge, and admin contract PASS markers.
These use host/mock callbacks where media is involved; physical board commands
are evidence procedures, not host substitutes.
The latest unchanged-tree bootstrap passed Stage 2/3 and reached the end of HIR
lowering at 5,492,252 KiB peak RSS, but Stage 4 failed on unresolved names from
partial/header-only import facades. H0 deployment and final SSpec remain
blocked until W1-C produces a full CLI.

## Merge and Review

- **Merge owner:** main implementation thread; resolves interfaces and owns the
  terminal boot verdict.
- **Host verifier:** runs each H0/H1 criterion once after integration and
  records the result against ST-001..ST-016.
- **Board operator:** records equipment, board serial/revision, boot mode, and
  artifact hashes before destructive tests.
- **Final reviewer:** independent highest-capability reviewer after H0/H1 is
  green, then repeats the review when the H2 evidence bundle is complete.
- **Release rule:** no commit/tag/release claim from this lane until the final
  report says `STATUS: PASS`; unrelated worktree changes stay outside the
  feature commit.
