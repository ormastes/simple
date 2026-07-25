# Paging + Swap Strategies for SimpleOS Across Six Architectures (MMU, no-MMU, Hosted)

**Status:** Research (not committed to any implementation yet)
**Date:** 2026-07-07
**Scope:** x86_64, x86_32, riscv64, riscv32, arm64 (AArch64), arm32 (ARMv7-A), cortex_m33 (no-MMU), and the Simple hosted runtime.
**Method:** 4 parallel web-research passes + 1 codebase survey, claims cross-checked against primary sources (Intel SDM, RISC-V Privileged spec, ARM ARM, kernel.org docs, mainline Kconfig). Provenance caveats are listed at the end of this document.

**Existing SimpleOS assets this research builds on:**
- Arch-neutral swap coordinator: `src/os/kernel/memory/memory_swap_coordinator.spl` (`MemorySwapCoordinator`: `swap_out_page`, `swap_in_page`, `restore_faulting_page`, `release_swapped`) with transactional VMM helpers (`memory_vmm_prepare_swap/commit_swap/rollback_swap`) in `memory_leveling_vmm.spl`.
- Runtime wiring: `src/os/kernel/memory/memory_swap_runtime.spl` (`memory_swap_runtime_handle_fault(virt_addr) -> i32`, PMM-pressure polling). Currently the fault hook is wired **only** on x86_64 (`src/os/kernel/interrupts/idt.spl:378`, via CR2).
- Per-arch paging code exists for all five MMU arches under `src/os/kernel/arch/{x86_64,x86_32,arm64,arm32,riscv64,riscv32}/paging.spl`, plus the arch-neutral `arch/common/paging_walker.spl` (`PagingTraits`) and `arch/hal.spl` (`hal_paging_*`, `hal_flush_tlb`).
- Related docs: `doc/04_architecture/simpleos_memory_leveling.md`, `doc/04_architecture/os/simpleos/kernel/simpleos_multiarch_hal.md`.

---

## 1. MMU paging per arch — minimal demand-paging model and what the swap coordinator needs

The arch-neutral coordinator needs exactly three things from each MMU arch:
(a) PTE bit access — present/valid, accessed, dirty;
(b) a TLB invalidation primitive, including a multi-core shootdown story;
(c) the faulting-VA register readable in the page-fault trap, plus fault-type decoding (read/write/exec).

### 1.1 x86_64 — 4-level paging

- IA-32e paging walks four in-memory structures rooted at CR3 — PML4 → PDPT → PD → PT — with Present, Read/Write, Accessed and (leaf) Dirty bits in each entry. [Intel SDM Vol. 3A, Ch. 4 "Paging" — https://cdrdv2-public.intel.com/812386/253668-sdm-vol-3a.pdf]
- On #PF the CPU loads **CR2** with the faulting linear address; a nested fault before the handler reads CR2 overwrites it — read CR2 first thing in the handler. [SDM Vol. 3A §4.7]
- **INVLPG is local to the executing logical processor only** — no broadcast. [https://www.felixcloutier.com/x86/invlpg (SDM Vol. 2A mirror)]
- x86 TLBs are not kept hardware-coherent across cores on page-table change; Linux does IPI-based shootdown (`smp_call_function_many` → local INVLPG on each target CPU). [https://docs.kernel.org/core-api/cachetlb.html]

Coordinator port needs: (a) direct P/A/D bits in PTE; (b) INVLPG + **IPI shootdown implemented by us**; (c) CR2 + #PF error code (W/U/P bits) for access type.

### 1.2 x86_32 — 2-level and PAE

- Non-PAE 32-bit paging is 2-level: 10-bit PD index, 10-bit PT index, 12-bit offset; 1024 x 32-bit entries per table. [SDM Vol. 3A §4.3]
- PAE is 3-level: 4-entry CPU-resident PDPTE set loaded from CR3, 64-bit entries, 512 entries/table, each PDPTE covering 1 GB. [SDM Vol. 3A §4.4]
- Fault/TLB model identical to x86_64: CR2, local INVLPG, IPI shootdown.

Coordinator port needs: same as x86_64; only the walker geometry differs (already abstracted by `paging_walker.spl`).

### 1.3 RISC-V — Sv32 / Sv39 / Sv48

- Sv32 (2-level, 32-bit VA), Sv39 (3-level, 39-bit VA), Sv48 (4-level, 48-bit VA); PTEs carry V, R, W, X, U, G, **A (accessed), D (dirty)** bits. [RISC-V Privileged Architecture, ratified — https://docs.riscv.org/reference/isa/v20240411/_attachments/riscv-privileged.pdf]
- `satp` CSR = MODE (Bare/Sv32/Sv39/Sv48/Sv57) + ASID + root-table PPN — the CR3 equivalent. [ibid., "Supervisor Address Translation and Protection Register"]
- On a page fault the faulting VA is in **`stval`**; `scause` = 12 (instruction), 13 (load), 15 (store/AMO page fault). [ibid.]
- **`SFENCE.VMA` is hart-local** — no architectural broadcast. Multi-hart shootdown goes through the **SBI Remote Fence extension**: `sbi_remote_sfence_vma(hart_mask, start, size)` (+ ASID variant). [RISC-V SBI spec, RFNC EID 0x52464E43 — https://docs.riscv.org/reference/platform-software/sbi/_attachments/riscv-sbi.pdf]
- Implementation caveat (flagged, not primary-sourced this session): the spec permits implementations to either set A/D in hardware or **raise a page fault when A/D would need setting** — the arch layer must treat "valid PTE but A=0/D=0 fault" as a fixup, not a swap fault.

Coordinator port needs: (a) V/A/D bits directly in PTE; (b) local `sfence.vma` + SBI remote fence for SMP (OpenSBI provides this on real boards, not QEMU-only); (c) `stval` + `scause` 12/13/15.

### 1.4 ARMv7-A — short-descriptor and LPAE

- Base VMSA uses the 2-level **short-descriptor** format; **LPAE** adds a 3-level long-descriptor format (PAE-like); `DFSR.LPAE` records which format generated a fault. [ARM ARM ARMv7-A/R DDI0406C — https://developer.arm.com/documentation/ddi0406/c/System-Level-Architecture/The-System-Level-Programmers--Model/The-Large-Physical-Address-Extension]
- **DFAR** holds the faulting VA of the last data abort; **DFSR** the status (distinct layouts short vs long descriptor). [DDI0406C, System Control Coprocessor chapter]
- TLB maintenance is CP15 c8 MCR ops (e.g. TLBIALL); visibility guaranteed only after **DSB + ISB**. SMP shootdown must be issued per-core (SGI/IPI) in the general case. [https://developer.arm.com/documentation/ddi0406/c/System-Level-Architecture/Virtual-Memory-System-Architecture--VMSA-/TLB-maintenance-requirements/General-TLB-maintenance-requirements]
- **No ARM-defined hardware dirty bit in the pre-LPAE short-descriptor format** — dirty tracking is software-managed: map writable pages read-only first, take the permission fault, set a soft-dirty bit, then upgrade the mapping (this is exactly what Linux does on ARM32).

Coordinator port needs: (a) present bit native; **A/D software-emulated** via permission-fault trick; (b) CP15 TLBI + DSB/ISB + SGI-based shootdown; (c) DFAR + DFSR (and IFAR/IFSR for prefetch aborts).

### 1.5 AArch64 — 4KB granule, TTBR0/TTBR1

- Split-root translation: **TTBR0_EL1** roots the low VA range (user), **TTBR1_EL1** the high range (kernel); range sizes set by **TCR_EL1** (T0SZ/T1SZ etc.). [https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/TCR-EL1--Translation-Control-Register--EL1-]
- **FAR_EL1** holds the faulting VA for synchronous instruction/data aborts taken to EL1. [https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/FAR-EL1--Fault-Address-Register--EL1-]
- **ESR_EL1** carries the exception class + ISS with DFSC/IFSC distinguishing translation vs access-flag vs permission faults. [https://developer.arm.com/documentation/ddi0595/2020-12/AArch64-Registers/ESR-EL1--Exception-Syndrome-Register--EL1-]
- **TLBI has hardware broadcast variants**: `TLBI VAE1IS` / `ALLE1IS` propagate invalidation across the Inner Shareable domain with **no software IPI**, bracketed by DSB (+ISB). [https://developer.arm.com/documentation/ddi0601/latest/AArch64-Instructions/TLBI-VAE1IS--TLBI-VAE1ISNXS--TLB-Invalidate-by-VA--EL1--Inner-Shareable]
- Implementation caveat (flagged, not primary-sourced this session): ARMv8.0 manages the Access Flag and dirty state **in software by default**; hardware A/D management (FEAT_HAFDBS, TCR_EL1.HA/HD) is an ARMv8.1 option. The arch layer must handle "access flag fault" (DFSC access-flag class) as a fixup, same shape as the RISC-V caveat.

Coordinator port needs: (a) valid bit native; A/D via access-flag-fault fixup path unless HAFDBS present; (b) `TLBI VAE1IS` — the cheapest shootdown of all six arches (no IPI); (c) FAR_EL1 + ESR_EL1.DFSC.

### 1.6 Summary table

| Arch | Levels | A/D bits | Fault VA | Local TLB inv | SMP shootdown |
|---|---|---|---|---|---|
| x86_64 | 4 (PML4) | HW | CR2 | INVLPG | software IPI |
| x86_32 | 2 / PAE 3 | HW | CR2 | INVLPG | software IPI |
| riscv64 | Sv39/Sv48 | HW **or** trap-fixup | stval | sfence.vma (hart-local) | SBI remote fence |
| riscv32 | Sv32 | HW **or** trap-fixup | stval | sfence.vma | SBI remote fence |
| arm64 | 4 @ 4KB granule | SW default; HW if FEAT_HAFDBS | FAR_EL1 | TLBI VAE1 | **TLBI *IS hardware broadcast** |
| arm32 | 2 short-desc / 3 LPAE | **SW only (pre-LPAE)** | DFAR | CP15 c8 + DSB/ISB | SGI/IPI |

The decisive design consequence: the coordinator must NOT assume hardware A/D bits. It needs a `pte_test_and_clear_accessed/dirty` hook that each arch may implement natively (x86) or via read-only-mapping + permission-fault soft bits (arm32, baseline arm64, trap-mode RISC-V).

---

## 2. Linux embedded no-MMU practice (CONFIG_MMU=n, uClinux heritage)

What "paging/swap" means without an MMU: **it doesn't exist**. Verified specifics:

- Under no-MMU Linux, anonymous private mappings are backed by *contiguous* page runs (no scatter, no COW); anonymous MAP_SHARED "behaves very much like private" because cross-fork sharing "doesn't support these" without an MMU; and MAP_SHARED+PROT_WRITE of a regular file is **not supported** at all. [https://www.kernel.org/doc/html/v5.14/admin-guide/mm/nommu-mmap.html]
- "Under uClinux there is no fork(), and clone() must be supplied the CLONE_VM flag" — no COW fork; vfork/clone(CLONE_VM) instead. [ibid.]
- **XIP** is a recognized no-MMU mapping mode: a private file mapping "may return a buffer that is not page-aligned... because XIP may take place" — code executes directly from flash/ROM. [ibid.]
- Writes to a shared no-MMU file mapping "are visible in other processes (no MMU protection)" — single flat address space, no isolation. [ibid.]
- Executable formats: **BINFMT_FLAT** (bFLT, via elf2flt) is execute-only, no dynamic linking; **FDPIC ELF** (fs/binfmt_elf_fdpic.c) supports dynamic linking and shared text in a single address space via function descriptors / GOT-relative addressing. [https://maskray.me/blog/2024-02-20-mmu-less-systems-and-fdpic]

### 2.1 Is swap literally unavailable on !MMU Linux? — YES, verified in Kconfig

- Mainline `mm/Kconfig`: `menuconfig SWAP ... depends on MMU && BLOCK && !ARCH_NO_SWAP`. **CONFIG_SWAP cannot be enabled when CONFIG_MMU=n.** [https://raw.githubusercontent.com/torvalds/linux/master/mm/Kconfig]
- `ARCH_NO_SWAP` is a separate arch override ("microblaze and nios2 hard code SWAP=n"). [ibid.]
- **ZSWAP** `depends on SWAP` → transitively MMU-only. [ibid.]
- **ZRAM itself `depends on BLOCK && SYSFS && MMU`** — zram cannot even be built on a no-MMU kernel. This kills any idea of "just use zram as the no-MMU swap workaround"; the compression *idea* transfers, the *mechanism* does not. [https://raw.githubusercontent.com/torvalds/linux/master/drivers/block/zram/Kconfig]

So Linux's answer on no-MMU is: no swap of any kind, XIP to keep code out of RAM, FLAT/FDPIC to share text, and careful static memory budgeting. That is 30 years of uClinux practice saying: **do not fake transparent paging without translation hardware.**

### 2.2 Flash-backed embedded: what replaces swap

- Embedded-Linux flash guidance is explicit: "Do not put a swap area on flash storage." [https://bootlin.com/blog/managing-flash-storage-with-linux/]
- Raw-flash `mtdblock` writes are read-modify-erase-rewrite with "no wear leveling of any sort" — swap's write pattern rapidly kills erase blocks (few thousand cycles on dense NAND). [ibid.]
- Where compression-instead-of-swap IS used (MMU systems): zram compressed-RAM block devices [https://www.kernel.org/doc/html/latest/admin-guide/blockdev/zram.html] and zswap compressed swap cache [https://www.kernel.org/doc/html/latest/admin-guide/mm/zswap.html] — Android/ChromeOS use zram to avoid flash swap I/O entirely.

### 2.3 Cortex-M MPU model

- The Cortex-M MPU is **region-based**: CMSIS `ARM_MPU_SetRegion(rbar, rasr)` defines each region by base address + size + access/execute attributes — there is no translation, no PTE, no remap-on-fault. [https://arm-software.github.io/CMSIS_6/main/Core/group__mpu__functions.html]
- Regions must be size-aligned and unconfigured addresses default to blocked (secondary source; ARM primary pages were fetch-blocked this session). [https://tickelton.gitlab.io/understanding-the-arm-cortex-m-mpu.html — flagged]
- Because a faulting access cannot be transparently satisfied by remapping (the address IS the physical address), **transparent demand-paged swap is impossible on MPU-only cores.** Real embedded alternatives (established practice; primary citations not fetched this session — flagged): cooperative/explicit segment swap (task explicitly loads/unloads a buffer), classic compile-time overlays (linker-planned code banks), and RAM compression of cold data via an explicit API.

---

## 3. Swap backing stores for embedded boards

| Store | FTL/wear leveling | Power-fail behavior | Verdict for swap |
|---|---|---|---|
| zram (RAM) | n/a — no flash writes | volatile by definition | **Default.** Zero wear, fast. |
| NVMe (enterprise) | internal FTL | capacitor PLP flushes in-flight writes + FTL map | Best disk-backed option |
| NVMe (consumer) | internal FTL | usually **no PLP caps**; FTL-map corruption possible on power cut | OK with transactional records |
| eMMC | internal controller (WL, ECC, bad-block) | ~512 B at-risk window, reverts to prior data (properly configured parts) | Acceptable |
| SD (consumer) | internal FTL, opaque | weaker/opaque power-fail guarantees; corruption risk | Avoid for swap; dev-only |
| raw NAND (MTD) | **none host-side** without UBI | torn writes + wear | **Never** (matches bootlin guidance) |

Sources:
- SLC ≥ ~100k P/E cycles vs MLC < 10k; UBI does host-side wear leveling for raw MTD (logical→physical erase-block map, per-PEB erase counters); UBIFS sits on UBI. [http://www.linux-mtd.infradead.org/doc/ubi.html, https://cateee.net/lkddb/web-lkddb/MTD_UBI_WL_THRESHOLD.html, https://docs.kernel.org/filesystems/ubifs.html]
- eMMC embeds the controller doing WL/ECC/bad-block/L2P itself, exposing a JEDEC block interface. [https://uavchip.com/blog/how-to-choose-flash-memory-embedded-systems.html — secondary]
- eMMC vs SD power-fail asymmetry. [https://www.embeddedts.com/assets/preventing-filesystem-corruption-in-embedded-linux]
- Enterprise NVMe capacitor-backed PLP vs consumer lack thereof. [https://www.howtogeek.com/id-love-it-if-consumer-ssds-had-this-feature-found-on-enterprise-ssds/ — secondary]
- zram + CONFIG_ZRAM_WRITEBACK (hybrid: idle/incompressible pages spill to a real device). [https://www.kernel.org/doc/Documentation/admin-guide/blockdev/zram.rst]

### 3.1 Implication for SimpleOS's transactional checksummed swap design

F2FS's crash model is the right precedent: **checkpoint + shadow paging** (new data goes to new locations, prior checkpoint stays valid; mid-write crash rolls back at mount) plus **roll-forward recovery** for fsync'd-but-uncheckpointed writes. [https://docs.kernel.org/filesystems/f2fs.html] The generic pattern for a swap store: each swap record = payload + **checksum + generation counter**, written to a *new* slot; the mapping entry flips to the new slot only after the payload write completes; on recovery, a bad checksum or stale generation simply means "that swap-out never happened" — which is always safe because the in-RAM page was not released until commit. SimpleOS's existing `memory_vmm_prepare_swap/commit_swap/rollback_swap` transaction shape in `memory_leveling_vmm.spl` is already the right skeleton; it needs the checksum+generation record format and ordered-write discipline (payload → flush → mapping flip) at the `MemorySwapBlockStore` layer.

---

## 4. Hosted-runtime "swap" for the Simple runtime

When the host OS (Linux/macOS/Windows) already pages and swaps, the runtime's job is *cooperation*, not reimplementation.

- `madvise(2)` lets a process hint reclaim behavior per address range. **MADV_DONTNEED** discards; **MADV_COLD** (Linux 5.4) deactivates pages — probable reclaim target, contents preserved; **MADV_PAGEOUT** (Linux 5.4) reclaims (swaps out) the range immediately. None apply to locked/HugeTLB/VM_PFNMAP pages. [https://man7.org/linux/man-pages/man2/madvise.2.html, https://lwn.net/Articles/790123/]
- `userfaultfd(2)` delivers page faults on registered VMAs to a userspace handler — true app-level demand paging. [https://man7.org/linux/man-pages/man2/userfaultfd.2.html] Real uses are niche and Linux-only: QEMU post-copy live migration [https://blog.linuxplumbersconf.org/2017/ocw/system/presentations/4699/original/userfaultfd_%20post-copy%20VM%20migration%20and%20beyond.pdf], CRIU lazy restore (non-cooperative mode, Linux 4.11+) [https://criu.org/Lazy_migration], and GC concurrent-compaction schemes [https://kernel-internals.org/mm/userfaultfd/].
- What real runtimes actually ship: **ZGC uncommits idle heap** back to the OS (JEP 351, 300 s default delay; Linux impl uses fallocate PUNCH_HOLE) [https://openjdk.org/jeps/351, https://wiki.openjdk.org/spaces/zgc/pages/34668579/Main]; **V8 decommits empty heap chunks with madvise** after GC [https://v8.dev/blog/optimizing-v8-memory].
- What data engines ship: **explicit spill-to-disk**, not custom paging — CockroachDB spills operator state when it exceeds its memory budget [https://www.cockroachlabs.com/blog/disk-spilling-vectorized/]; SQL Server spills to tempdb on memory-grant overflow [https://learn.microsoft.com/en-us/sql/relational-databases/memory-management-architecture-guide?view=sql-server-ver17]; the classic algorithm is external merge sort [https://15445.courses.cs.cmu.edu/spring2024/notes/10-sorting.pdf].

**Verdict:** userfaultfd is NOT worth adopting for the hosted tier — Linux-only, needs a fault-service thread, races with host reclaim and with GC/compaction, and its benefit (page-granular transparent lazy fill) solves migration/checkpoint problems Simple doesn't have. Adopt instead: (1) madvise hints (COLD/PAGEOUT under pressure; DONTNEED/FREE for dead arenas) with no-op fallbacks on non-Linux, matching the ZGC/V8 pattern; (2) an **explicit spill API** for large structures, matching the database pattern — which is exactly the same API the no-MMU tier needs, so it is written once.

---

## 5. Recommended layered architecture

```
                    +--------------------------------------+
                    |  MemorySwapCoordinator (exists)      |
                    |  policy, leveling, transactions       |
                    +---+----------------+-------------+---+
                        |                |             |
              Tier A: MMU hooks   Tier B: no-MMU   Tier C: hosted
              (per-arch trait)    segment store     adapter
                        |                |             |
   x86_64 x86_32 rv64 rv32 arm64 arm32   cortex_m33    linux/macos/win
                        |
              MemorySwapBlockStore backends:
              zram-like compressed RAM (default) | eMMC/NVMe partition
              (checksummed, generation-countered records) | never raw NAND
```

### 5.1 Tier A — per-arch MMU hook interface (the exact hook list)

Add to `arch/hal.spl` / `arch/common/paging_walker.spl` a `MmuSwapHooks` trait; the coordinator consumes only this:

1. `fault_info() -> SwapFaultInfo { fault_va, access: Read|Write|Exec, kind: NotPresent|Permission|AccessFlag }`
   — x86: CR2 + #PF error code; RISC-V: stval + scause 12/13/15; arm64: FAR_EL1 + ESR_EL1.DFSC; arm32: DFAR/DFSR (+ IFAR/IFSR).
2. `pte_read(space, va) -> PteView { present, accessed, dirty, writable, phys }`
3. `pte_make_nonpresent_keep_swap_slot(space, va, swap_slot_token)` — encode the swap-slot id in the non-present PTE's software bits (all six MMU formats leave ignored bits in non-present entries).
4. `pte_install(space, va, phys, prot)` — swap-in completion.
5. `pte_test_and_clear_accessed(space, va) -> bool` — native on x86/RISC-V-HW-A/D; soft-bit + access-flag-fault fixup on arm64-without-HAFDBS, arm32, trap-mode RISC-V.
6. `pte_test_and_clear_dirty(space, va) -> bool` — same split; arm32 short-descriptor is ALWAYS software (write-protect + permission-fault promotion).
7. `tlb_invalidate_page_local(va, asid)` — INVLPG / sfence.vma / TLBI VAE1 / CP15 c8 + DSB/ISB.
8. `tlb_shootdown(va_range, asid, cpu_mask)` — x86: IPI loop; RISC-V: `sbi_remote_sfence_vma`; arm64: `TLBI VAE1IS` + DSB (no IPI needed); arm32: SGI-driven per-core invalidate. Single-core boots implement it as the local call.
9. `ad_fixup_fault(fault_info) -> bool` — handles access-flag/dirty-emulation faults BEFORE the coordinator's `restore_faulting_page` runs; returns true if it was a bookkeeping fault, not a swap fault. (This is the hook the summary table in §1.6 forces into existence.)

Wiring rule: every arch's fault handler routes through `ad_fixup_fault` then `memory_swap_runtime_handle_fault` — today only `interrupts/idt.spl:378` (x86_64) does; `arch/riscv64/riscv_mmu_trap.spl` has its own fault path that must be converged.

### 5.2 Tier B — no-MMU (cortex_m33): compressed-RAM segment store + explicit spill API

Grounded in §2: Linux flatly gates SWAP (and even zram) on MMU, and the MPU cannot remap — so **do not fake transparent paging**. Instead:

- `SegmentStore`: explicit handles — `spill(handle)` compresses the segment into a compact RAM pool (zram's idea, reimplemented as a library since the kernel mechanism is MMU-gated); `pin(handle) -> ptr` decompresses back; `unpin(handle)` re-permits spilling. Access while unpinned is a program error, optionally hardened by MPU no-access regions on the segment's home while spilled (fault = misuse trap, not demand paging).
- XIP-first budgeting: keep code in flash (Cortex-M's native model per §2), reserve RAM for data segments.
- The `spill/pin` API surface is deliberately identical to the hosted tier's large-object spill API (§4) so `nogc_async_mut_noalloc` code is portable across both.

### 5.3 Tier C — hosted adapter

- Pressure hints: `madvise(MADV_COLD)` on cold arenas, `MADV_PAGEOUT` under runtime-detected pressure, `MADV_DONTNEED` on freed arenas; compile to no-ops where unsupported (macOS/Windows analogues optional later).
- Explicit spill-to-disk for large structures (same API as Tier B, backed by temp files, external-merge-sort style for ordered data).
- **No userfaultfd** (per §4 verdict).

### 5.4 Arch → tier map

| SimpleOS target | Tier | Fault reg | Shootdown | A/D strategy |
|---|---|---|---|---|
| x86_64 | A | CR2 | IPI | hardware |
| x86_32 | A | CR2 | IPI | hardware |
| riscv64 (Sv39) | A | stval | SBI RFNC | HW or trap-fixup |
| riscv32 (Sv32) | A | stval | SBI RFNC | HW or trap-fixup |
| arm64 | A | FAR_EL1 | TLBI *IS (hw broadcast) | SW default, HW if HAFDBS |
| arm32 (ARMv7-A) | A | DFAR | SGI/IPI | software only |
| cortex_m33 | B | (MPU fault = misuse) | n/a | n/a |
| hosted runtime | C | n/a | n/a | n/a |

All Tier-A mechanisms are ISA-architectural (SDM / Privileged spec / ARM ARM) and SBI is standard firmware (OpenSBI ships on real RISC-V boards) — **nothing here is QEMU-only**. QEMU `virt`/`q35` machines for all six arches serve as the provable first target; the same code carries to real boards (any RV64 SBC, Raspberry Pi-class arm64, STM32-class M33).

---

## 6. Phased implementation recommendation

**Phase 0 — Hook trait extraction (x86_64 reference).** Define `MmuSwapHooks` (§5.1, hooks 1–9) in `arch/common`; implement for x86_64 from the existing `arch/x86_64/paging.spl` + `idt.spl` wiring. Add the swap-slot-in-nonpresent-PTE encoding (hook 3) and the `ad_fixup_fault` no-op (x86 has HW A/D). Gate: existing coordinator specs pass unchanged through the trait; QEMU q35 swap-out/fault/swap-in round-trip spec.

**Phase 1 — Backing-store hardening.** Extend `MemorySwapBlockStore` records with checksum + generation counter and ordered commit (payload → flush → map flip), per the F2FS-inspired model (§3.1). Add the compressed-RAM store (zram-equivalent) as the default backend. Gate: power-cut simulation spec (kill mid-swap-out at every ordering point; recovery never loses a committed page, always discards torn records).

**Phase 2 — riscv64 + arm64 ports.** riscv64: converge `riscv_mmu_trap.spl` onto the hook trait (stval/scause; `sbi_remote_sfence_vma` for SMP; trap-mode A/D fixup). arm64: FAR_EL1/ESR_EL1 decode, TLBI VAE1IS shootdown, software access-flag fixup (HAFDBS detection later). Gate: same round-trip spec green on QEMU virt for both, SMP shootdown spec with 2+ harts/cores.

**Phase 3 — 32-bit ports (x86_32, riscv32, arm32).** Mostly walker geometry; arm32 additionally needs the full software-dirty emulation (write-protect + permission-fault promotion) — build it as the shared `ad_fixup_fault` soft-bits library that arm64-without-HAFDBS also uses. Gate: round-trip spec on QEMU for all three.

**Phase 4 — Tier B no-MMU segment store (cortex_m33).** `SegmentStore` spill/pin/unpin over a compressed RAM pool + optional MPU no-access hardening. Gate: QEMU mps3-an547 (or equivalent M33 machine) spec exercising spill/pin under memory pressure.

**Phase 5 — Tier C hosted adapter.** madvise hint layer (Linux first, no-op elsewhere) + the shared explicit-spill API backed by temp files. Gate: hosted spec showing RSS reduction after MADV_PAGEOUT on a cold arena (Linux CI), spill/restore correctness everywhere.

Order rationale: Phase 0/1 de-risk the shared 80% (trait + crash-safe store) on the already-wired arch; Phases 2–3 are then mechanical per-arch fills; Tiers B/C are independent and can proceed in parallel with Phase 3.

---

## Appendix: source provenance and verification caveats

Environment note: WebFetch and curl/wget were hook-blocked for the research agents this session, and the ctx_* MCP fetch tools were not actually registered. Verification levels achieved:
- **Directly fetched and inspected** (highest confidence): kernel.org nommu-mmap doc, mainline `mm/Kconfig` and `drivers/block/zram/Kconfig` raw files, CMSIS MPU API docs, maskray FDPIC article, bootlin flash guide — i.e., all §2 claims including the CONFIG_SWAP/ZRAM MMU gating.
- **Search-verified with attributed verbatim excerpts, cross-checked against the linked official page** (high confidence, but no raw full-document fetch): Intel SDM Vol. 3A, RISC-V Privileged + SBI specs, ARM ARM DDI0406C/DDI0601/DDI0595, man7 madvise/userfaultfd, LWN 790123, JEP 351, F2FS/zram/zswap/cachetlb kernel docs, CRIU wiki, V8 blog, CockroachDB/SQL Server docs.
- **Flagged lower-confidence / secondary**: eMMC-vs-SD power-fail specifics (embeddedts), NVMe PLP (howtogeek), MPU region alignment behavior (tickelton.gitlab.io), SLC/MLC endurance figures (cateee.net lkddb), torn-write definition; plus two unsourced-but-load-bearing implementation caveats explicitly marked inline: RISC-V trap-mode A/D and AArch64 FEAT_HAFDBS defaults — re-verify both against the Privileged spec §"Memory Privilege" A/D text and ARM ARM D5.4 before writing the arm64/riscv fixup code.
- Two Linux-practice claims in §1 (ARM32 software-dirty via permission fault; Linux IPI shootdown detail) are standard kernel behavior sourced to docs.kernel.org/core-api/cachetlb.html at snippet level.
