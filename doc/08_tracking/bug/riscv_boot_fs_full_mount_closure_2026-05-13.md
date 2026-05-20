# RISC-V boot filesystem full mount closure is not freestanding-safe

Date: 2026-05-13
Fixed: 2026-05-20
Status: Fixed
Severity: Production blocker for mounting the full NVFS/VFS root in the RV64 production ELF

## Evidence

The RV64 boot image now proves live `virtio-blk-pci` reads and an NVFS
superblock probe from disk, but the existing full boot filesystem path is not
ready to import into the production freestanding closure.

Command:

```bash
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/debug/simple native-build \
  --source build/os/generated --source src/os --source src/lib \
  --backend llvm --opt-level=aggressive --log on --timeout 180 \
  --entry src/os/kernel/boot/boot_fs.spl --entry-closure \
  --target riscv64gc-unknown-none -o /tmp/boot-fs-rv64.elf
```

Initial observed result:

- `src/os/kernel/boot/boot_fs.spl`, `src/os/services/vfs/vfs_boot_init.spl`, and
  `src/os/services/vfs/vfs_block_adapters.spl` pass `bin/simple check`.
- The native freestanding closure build fails after pulling hosted/userland
  process and window dependencies through `spawn_binary`/loader/VFS paths.
- Final failure observed: `src/os/userlib/window_part3.spl` LLVM codegen reports
  `semantic: llvm global load referenced undeclared symbol val`.

Follow-up after fixing the local `_push_u64` typo in
`src/os/userlib/window_part3.spl`:

- The same diagnostic build reaches the freestanding unresolved-symbol phase.
- It reports `156 unexpected symbol(s)` and `149 candidate symbol(s)` deferred to
  the linker.
- Stub generation then fails in `_stubs_freestanding.c` because generated
  `__stub_compat_rt_is_some` calls undeclared `__stub_compat_rt_is_none`.

Follow-up after fixing freestanding compatibility stub generation in
`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`:

- The same diagnostic `boot_fs.spl` RV64 freestanding closure links.
- It still reports the broad candidate surface before linker GC, including
  hosted/userland symbols such as `current_architecture`, window protocol
  conversions, and `KLogEntry.from_bytes`.
- This proves the generated-stub crash is fixed, but does not make the full
  `boot_fs_sequence()` safe to call from `os_main`; the call would make more of
  the hosted launch path live.

## Impact

`os_main` should not import and call `boot_fs_sequence()` yet. Doing so risks
making the hosted launch path live in the currently passing RV64 production boot
image. The safe current boundary is the freestanding storage gate: live VirtIO
block device initialization plus NVFS superblock validation and explicit
filesystem-superblock readiness.

## Required Fix

Split boot filesystem mounting into a freestanding-safe probe/mount slice before
user process launch. The first production slice should avoid hosted window,
process, syscall, and full app-registry dependencies, and should consume the
existing RV64 C block read bridge or a Simple BlockDevice wrapper around it.

## Verification Target

The blocker is fixed when a production RV64 native build can import the full
boot filesystem mount path into `os_main` and still report zero unexpected
freestanding unresolved symbols, followed by a QEMU run that proves NVFS root
mounted from `virtio-blk-pci`.

## Fix Applied (2026-05-20)

Root cause: `boot_fs_mount.spl` imported `CNvmeBlockAdapter` from
`os.services.vfs.vfs_block_adapters`.  That module co-locates
`CNvmeBlockAdapter` with `NvmeBlockAdapter`, which imports
`os.drivers.nvme.nvme_driver.{NvmeDriver, DmaAddrs}`.  The module-level
`use` of `NvmeDriver` caused the linker to pull in `syscall`-based DMA
allocation (syscalls 83, 84, 26) and related hosted symbols into the
freestanding closure even though `NvmeBlockAdapter` was never instantiated.

Fix:
1. Created `src/os/kernel/boot/c_nvme_adapter.spl` — a freestanding-safe
   duplicate of `CNvmeBlockAdapter` (renamed `CNvmeBlockAdapterFs`) that
   imports only `std.fs_driver.block_device`, `os.kernel.boot.mmio`, and
   `os.kernel.log.klog_api`.  No `NvmeDriver`, no `syscall`, no `pcimgr`.
2. Updated `boot_fs_mount.spl` to import `CNvmeBlockAdapterFs` from the new
   module instead of `CNvmeBlockAdapter` from `vfs_block_adapters`.
3. Added `test/kernel/boot_fs_mount_spec.spl` — type and initial-state tests
   for the freestanding mount path that import no hosted symbols.

`os_main.spl` was already correct (calls `boot_fs_mount_freestanding()`, not
`boot_fs_sequence()`).  `boot_fs.spl` is retained unchanged as the hosted
mount + spawn path for non-freestanding use.
