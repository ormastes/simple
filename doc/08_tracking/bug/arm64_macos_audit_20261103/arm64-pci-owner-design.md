# ARM64 PCI/ivshmem owner repair design — 2026-11-03

Status: proposed, NOT implemented or native-admitted. Bug `arm64_qemu_ivshmem_preboot_2026-07-12`; claim `simpleos-arm64-pci-20261103` managed by bug DB lead. Source reviewed against release `4cc3cd4a800837eb21dd4d2d83303e50cb5d32d7` (relevant files unchanged from firmware worktree). MDSOC kernel/drivers only; no userland ECS state.

## Proven broken call chain

`gui_entry_desktop_start` -> `map_qemu_host_gpu_ivshmem_bar2` -> `pci_read_vendor` -> `pci_read_config` currently executes x86 port-I/O on ARM64. ARM64 write override calls `_pci_ecam_base()`, literal zero. The ARM64 C runtime has a separate hardcoded ECAM scan; its constants are not accepted firmware resources and do not repair the Simple owner.

The canonical unified `crt0.S` explicitly ignores the Linux Image x0 DTB argument. `.Lreloc_check` overwrites x0 for logging. Its relocation trampoline only uses x2-x5 and x9-x17; x20 is available in the boot portion, before exception code. After relocation, EL changes, stack and BSS setup, `_c_start(void)` calls `spl_start(void)`. Separate `os.kernel.arch.arm64.boot_main(dtb_addr)` neither consumes the argument nor belongs to this desktop closure. There is no ARM64 PciHostDescriptor constructor.

## Owner boundaries and proposed names

1. Startup ABI boundary: `rt_arm64_boot_dtb_address() -> u64` exposes only the **raw untrusted** saved address. Preserve x0 in x20 at `.Lreloc_check` before any clobber, and publish it to a boot-owned scalar only after BSS clearing. Do not change the public zero-argument `spl_start` ABI or store into BSS before it is cleared. A getter never claims valid DTB or ready PCI. Existing C runtime may consume the getter but must not independently parse PCI or choose addresses.
2. Kernel boot: `arm64_pci_boot_init_from_dtb(dtb_addr: u64) -> Result<PciHostDescriptor, text>` owns boot-memory validation, parsing and exactly-once provider admission. Store no ambient default host. Zero/missing/invalid handoff is an error before any PCI access.
3. Kernel FDT adapter: `fdt_pci_host_from_blob(blob: FdtBlob) -> Result<PciHostDescriptor, text>` normalizes checked firmware resources. Reuse `FdtBlob`, `fdt_find_compatible`, `fdt_node_prop`, `fdt_node_reg`, `fdt_node_enabled`, and `pci_host_descriptor_reason`. A byte-fixture caller takes exactly this route.
4. PCI driver: `pci_ecam_read32(host: PciHostDescriptor, target: PciConfigTarget) -> Result<u32, text>` and `pci_ecam_write32(host: PciHostDescriptor, target: PciConfigTarget, value: u32) -> Result<bool, text>` validate target and address, then use the existing `mmio_hardware` volatile access/barrier owner. Preserve x86's existing port-I/O branch explicitly; no wildcard fallback or zero-base branch.
5. PCI window adapter: `pci_host_bar_cpu_address(host, pci_base, size, kind) -> Result<u64, text>` finds a matching declared window and translates PCI address to CPU physical address with checked arithmetic. ivshmem receives the descriptor and returns mapped CPU address plus size, not only slot number from which callers reconstruct an architecture constant. Scope ARM64 first; preserve current x86 caller contracts with a distinct adapter.

## Boot-memory and mapping contract — prerequisite, not optional

Saving the address is insufficient: relocation copies the image to the link address, uses a scratch trampoline above the loaded image, then clears BSS and allocates heap. None may overwrite firmware DTB bytes before parsing.

Before allowing a usable DTB handle, establish a bounded 40-byte header read inside firmware-readable RAM; bound totalsize to the existing 2 MiB FDT limit; reject wraparound, misalignment and overlap with relocation destination, trampoline scratch, the full final `[_start, _kernel_end)` region (including the C runtime 512 MiB BSS heap, linker stack and heap), plus scratch trampoline extent. If boot cannot establish that memory range, fail closed or first copy into a reserved boot-owned buffer before any conflicting write. The reserved buffer must itself survive relocation and BSS, and be excluded from allocator ownership. Do not represent a raw x0 pointer as validated merely because `FdtBlob.at_address` accepts it.

The current unified entry has MMU/caches disabled, so approved ECAM and BAR CPU physical regions can use identity access through `mmio_hardware`. That is an explicit boot-mode precondition, not a general mapping implementation. A future MMU-enabled entry must use ARM64 paging/MMIO mapping ownership and return mapped virtual addresses. It must not reuse this identity provider with SCTLR.M enabled. Validate ECAM aperture and BAR windows before identity publication; no guessed QEMU ECAM constant.

## FDT PCI parsing contract

- Validate FDT total size and structure/string block extents; validate each complete property interval against both the property block and total blob. Existing byte access returns zero outside the blob and is not sufficient to reject truncation.
- Select exactly one enabled `pci-host-ecam-generic` host for the intended domain. Multiple ambiguous hosts are an error until caller domain selection exists.
- Host `reg` is decoded with parent address/size cells via `fdt_node_reg`; require nonzero aligned ECAM base, nonzero bus-sized aperture and checked end. Only known-supported parent cell widths are accepted.
- Parse `bus-range` as exactly two big-endian u32 values, both <=255, start<=end; require represented bus count <= ECAM size / 1 MiB. Do not silently truncate oversized cells.
- Parse host's OWN `#address-cells` and `#size-cells` for `ranges`: PCI child address cells are three, distinct from parent cells stored on FdtNode. Each tuple includes PCI space/flags, child PCI address, parent CPU address, size. Reject wrong stride/truncation, unsupported spaces, zero sizes, end overflow and ambiguous overlapping windows; retain nonprefetchable and prefetchable64 identities.
- Parent address translation is not implemented by the existing FDT reader. First slice must accept only a provably untranslated root host or checked identity ancestors; reject nonidentity ancestor `ranges` until a correct translation owner exists. Never assume `/soc` identity from a name.
- `dma-ranges`/coherency are recorded truthfully. ivshmem shared-memory mapping must not advertise general DMA support from missing properties. Domain and unsupported cells fail explicitly.
- Tighten shared `pci_host_config_addr` contract before use: device<32, function<8, dword-aligned offset<=4092, checked ECAM base+size and base+offset arithmetic. Invalid accesses perform no MMIO.

## Wiring and failure semantics

The ARM64 pure-Simple board entry invokes `arm64_pci_boot_init_from_dtb(rt_arm64_boot_dtb_address())` before `gui_entry_desktop_start` can enumerate host GPU PCI. Propagate an unavailable reason instead of synthesizing all-ones reads as successful initialization. Device-not-present remains a distinct enumeration result after a valid MMIO read. Failed provider admission performs no BAR probe/write, no default-address memory access and no fake GPU-ready receipt.

Initialize once while boot owns mutable PCI discovery; retain a single immutable admitted descriptor. Configuration cycles and BAR probe/restore are owned serially by the driver. No mutable descriptor or MMIO pointer crosses into app state. BAR reads/writes for probes need explicit error-aware restore of command/BAR state.

## Meaningful fixtures and admission

1. Handoff: cross-assemble real production startup; inspect save-before-clobber and publish-after-BSS. Exercise actual assembly getter/publication in a tiny static ARM64 qemu-user fixture, including zero and high-bit addresses, caller-saved clobbers, simulated BSS clear and repeated reads. This proves scalar ABI only, not full boot/relocation or DTB-byte survival. Test destination/scratch/BSS overlap arithmetic separately with non-overlapping and wraparound cases.
2. FDT: build valid binary blobs with root PCI ECAM reg, bus-range and multiple windows; drive the actual Simple parser. Mutate truncation, property length, cells, disabled node, ambiguous nodes, bad compatible, ranges translation, bus overflow, ECAM/window overflow and config targets. Assert exact descriptor values and failure reasons; no string-presence-only tests.
3. MMIO: controlled existing test owner records exact read/write addresses and barriers. Assert wrong targets make zero calls; verify bus-start normalization, 64-bit ECAM address preservation, BAR read/probe/restore, CPU/PCI translation and x86 regression path.
4. Current compiler must compile/link/run the focused Simple suite before any production landing. No available admitted runtime result has been recorded for this new owner yet; no fallback to Rust seed.
5. Native acceptance requires current-source ARM64 real-firmware boot, live ivshmem vendor/device discovery, valid 8 MiB BAR2 CPU mapping, and correlated GPU frame receipts. No host fixture can close that bar.

## Bounded delivery and review

A: saved raw handoff + checked boot range owner; B: checked FDT descriptor adapter + host fixtures; C: ECAM access/BAR mapping + ARM64 board wiring; D: native gate after root grants slot. Do not land A/B as an ivshmem fix or set bug pending based on disconnected code. If kernel/drivers-only scope excludes startup boundary changes, A is a concrete blocking dependency rather than permission to invent the DTB address.

No recursive agents. Existing ARM64 native peer reviews handoff fixtures; DB crosscheck supplied parser/owner audit. Sidecar lanes: N/A. Merge owner: bug DB lead; final source/interface reviewer: root Astra architectural reviewer. Shared interface names above must be reviewed before production edits. User acceptance: target-correct repair; no new architecture choice is being silently selected.


## Unlanded prerequisite candidate checkpoint

Worktree `/tmp/arm64-pci-handoff-candidate-20261103`, base release `4cc3cd4a800`. Only `examples/09_embedded/simple_os/arch/arm64/boot/crt0.S` changed: save x0 into reserved x20 at `.Lreloc_check`, publish scalar after `.Lbss_done`, export `rt_arm64_boot_dtb_address` backed by local `.bss.boot_handoff`. The 30-line addition does not dereference DTB memory, choose MMIO addresses or admit PCI. No production commit/PR/merge yet. Independent handoff fixture owner is `/root/bug_db_lead/arm64_native`; exact source hash/object/disassembly and execution results under `arm64-dtb-fixture/`. This is a candidate for ABI review, not the complete bug repair.


## Reviewed prerequisite merge

Raw scalar handoff prerequisite merged through PR #6394, merge `c348b50e13b348b5620c7e4b74dc988888df4ae2`, reviewed head `bfc7a441ce0ef1f967b3abd2ccdbe7b02892e903`. Astra exact-head review found no P0/P1 within that limited scope. Repo checker `scripts/check/check-arm64-boot-dtb-handoff.py` retains the reproducible exact-source fixture. Full production assembly, five reduced ARM64 fixture outcomes, packaging equivalence and nine blocking push checks passed as documented. No firmware/native admission or DTB-byte ownership claim. The PCI issue remains open/fixing; parser/provider/BAR steps above are not implemented. Current worktree remains sparse at 128572 KiB; root may remove it after collecting artifacts since its owned change is merged.
