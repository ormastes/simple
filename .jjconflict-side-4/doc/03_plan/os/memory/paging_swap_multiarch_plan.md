# Plan: paging + swap on all arches (baremetal + hosted + no-MMU)

Status: PLANNED 2026-07-13. Research:
`doc/01_research/os/memory/paging_swap_multiarch_research.md` (landed
`f4142398571`). Requirement (user): paging/swap on baremetal SimpleOS and the
hosted Simple runtime where an MMU exists; x86, riscv, arm/aarch64; follow
Linux embedded practice; a no-MMU tier as well. Everything board-workable —
QEMU-provable first, no QEMU-only mechanism.

## Ground truth (recon 2026-07-13, file:line verified)

- Paging + per-process address spaces ALREADY EXIST on all six MMU arches:
  x86_64 4-level (`arch/x86_64/paging.spl`), x86_32 2-level, arm64 4-level
  TTBR0 (`arch/arm64/paging.spl`), arm32 short-descriptor, riscv64 Sv39
  (`arch/riscv64/paging.spl` + `riscv_mmu_trap.spl`), riscv32 Sv32 — bridged
  by `src/os/kernel/memory/user_address_space.spl` (@cfg). All six have
  bootable QEMU lanes (`platform_target_catalog.spl`).
- Transactional checksummed swap EXISTS but is x86_64-coupled at exactly one
  seam: `memory_swap_runtime.spl:10` imports `PTE_PRESENT`/`vmm_read_pte`
  from the x86_64 vmm; fault hook wired only in x86_64 (`idt.spl:378`).
  Coordinator + block store are arch-neutral. `trait HalPaging`
  (`arch/hal.spl:112-120`) exists but lacks PTE-bit/fault/TLB hooks.
- cortex_m33: MPU-only, no MMU, no QEMU lane (board/vendor tools only).
- Backing stores: NVMe (x86_64 proven), virtio-blk (arm64 in use). No
  SD/eMMC driver yet (board gap, tracked).
- Hosted runtime: no mmap/madvise usage anywhere — hosted tier is greenfield.

## Key research findings that constrain the design

1. Linux `mm/Kconfig`: `SWAP depends on MMU && BLOCK` — no transparent swap
   without an MMU, ever (zram too). The no-MMU tier must be explicit, not
   fake-transparent.
2. The coordinator must NOT assume hardware accessed/dirty bits: arm32
   short-descriptor has no HW dirty bit; ARMv8.0 baseline manages A/D in
   software; RISC-V may trap instead of setting A/D. → mandatory
   `ad_fixup_fault` hook + a shared software-dirty library for the 32-bit
   arches.
3. Fault info: CR2 (x86) / stval+scause 12,13,15 (riscv) / FAR_EL1+ESR_EL1
   (arm64) / DFAR+DFSR (arm32). TLB: INVLPG and SFENCE.VMA are core-local
   (IPI / SBI remote-fence for shootdown); AArch64 TLBI ...IS broadcasts in
   hardware.
4. Backing stores: compressed-RAM (zram-style) default (zero wear);
   eMMC/NVMe OK with the existing checksummed generation-countered records;
   raw NAND swap categorically ruled out.
5. Hosted: madvise(MADV_COLD/PAGEOUT) hints + explicit spill-to-disk;
   userfaultfd rejected (Linux-only, complexity without need).

## MmuSwapHooks trait (Tier A interface — 9 hooks)

fault_info() -> (addr, kind); pte_read(as, va); pte_install(as, va, pte);
pte_make_nonpresent(as, va) -> old; test_and_clear_accessed(as, va);
test_and_clear_dirty(as, va); tlb_invalidate_local(va);
tlb_shootdown(as, va); ad_fixup_fault(as, va, kind) -> bool.
Home: extend `trait HalPaging` in `src/os/kernel/arch/hal.spl` (or a sibling
trait in the same file); per-arch impls live in each arch dir.

## Phases

- **P0 — trait extraction on x86_64 (no behavior change).** Introduce the
  hooks, re-point `memory_swap_runtime.spl` at them, x86_64 impl backed by
  the existing vmm functions. GATE: existing swap lanes stay green
  (`memory_leveling_pressure_swap_spec.spl`,
  `check-simpleos-memory-leveling-qemu.shs`) — byte-identical serial ladder.
- **P1 — compressed-RAM swap backend (zram-style).** A second SwapBlockStore
  impl: compressed pages in a reserved RAM pool (arch-neutral). GATE: swap
  roundtrip through the RAM backend on x86_64 QEMU; checksum-tamper test
  fails closed.
- **P2 — riscv64 + arm64 hook impls.** Wire fault paths (riscv trap →
  coordinator; arm64 sync-exception → coordinator), software-A/D fixups
  where needed, SBI remote-fence / TLBI-IS shootdown. Backing: virtio-blk or
  P1 RAM backend. GATE: per-arch QEMU swap-roundtrip lane (boot → pressure →
  swap-out marker → touch → fault → swap-in marker → checksum-verified).
- **P3 — x86_32 + riscv32 + arm32.** Shared software-dirty library; same
  gates on their QEMU lanes.
- **P4 — no-MMU tier (cortex_m33).** Explicit `SegmentStore`
  spill/pin/unpin API over a compressed RAM pool; optional MPU no-access
  hardening on spilled segments. NOT transparent paging. GATE: host-side
  unit specs + AN505 QEMU MPU lane where applicable; board evidence per the
  board-hardening plan.
- **P5 — hosted adapter.** `std.memory_leveling`-integrated
  madvise(MADV_COLD/PAGEOUT) hints + explicit spill API for large
  structures; only where measurably better than host-OS default swap. GATE:
  hosted spec with RSS evidence.

## Board-workability

All mechanisms are ISA/firmware-standard (OpenSBI on riscv boards, PSCI/GIC
on arm). Compressed-RAM backend removes the disk dependency on boards
without safe swap media. eMMC/SD driver remains the tracked hardware gap for
disk-backed swap on boards (same P-series as the NIC gap in
`doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`).
