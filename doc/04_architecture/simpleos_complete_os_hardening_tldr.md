<!-- codex-architecture -->
# SimpleOS Complete OS Hardening — TLDR

Purpose: converge existing SimpleOS subsystems into one authenticated, measurable, three-architecture OS without creating parallel owners.

Core decisions:

- Keep `FsDriver`/`DriverInstance`/`MountTable` and `WmService` as canonical owners.
- Shared V1 records live in `common`; mutable VFS, loader, lifecycle, WM, and evidence owners stay tree-private.
- Resolve/open once, authenticate the handle, then register it in private generational loader state; copied Simple values never carry execution authority.
- Workers return bounded generation-tagged results; parent owners validate and commit deterministically.
- QEMU, native-host, and physical-board receipts remain distinct rows in one ledger.

Critical path:

`contracts/evidence → filesystem convergence → authenticated exec → target Simple roles → LLVM/userland → servers/WM → QEMU+physical campaigns → perf/security/duplication verify`

Hot-path rules: generation-bound caches with complete invalidation; streamed executable reads; no full-tree scans/raw-source execution/per-request server spawns; one WM render/present owner.

Current boundary: VFS handle lookup/release is O(1), bounded VFS reads close handles on every path, and initramfs/installer payload admission uses canonical ELF/SMF owners and blocked rows instead of fabricated files. FAT32 now uses bounded generation-stamped handles and per-mounted-instance acknowledged flush promotion; NVFS arena/superblock recovery shares one device owner with checksum-valid replicated commit records, while mounted NVFS/NVFS-POSIX durability remains fail-closed. Changeable installer host artifacts now fail closed with `bounded-nofollow-fd-reader-unavailable`; the hosted file API still lacks a no-follow descriptor-bound fstat/read owner. The seven-category primary-tool manifest keeps four rows unavailable and reports checksum, text (`grep`), and process (`ps`) as blocked behind target/filesystem execution receipts. Evidence state and loader authority use checked owner boundaries but remain unadmitted pending runtime proof. The scheduler adoption transaction consumes only an opaque loader token and never returns raw address-space authority; task, vmspace, capability, and ready publication now shares the canonical mutable `Scheduler.me` owner, while indeterminate transitions remain queryable and unauthorized. Shared HTTP/DBD TLS framing now uses one mutable fixed ring with authenticate-before-commit and linear one-byte-fragment work. Cryptographic admission, admitted runtime proof, ARM/RISC-V mapping reclamation, mounted NVFS durability, target-native toolchains, complete protocols, and target/runtime campaigns remain release blockers.

Inspect next:

- `src/lib/nogc_async_mut/fs_driver/`
- `src/os/kernel/loader/`
- `src/lib/common/contracts/execution/`
- `src/os/services/wm/wm_service.spl`
- `doc/05_design/simpleos_complete_os_hardening.md`
