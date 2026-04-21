# ARM FS Exec ARM32 Resume - 2026-04-21

## Status
- ARM64 `arm64-virtio-fat32-smf` boots under QEMU, reads `/sys/apps/hello_world.smf` from FAT32, creates the user task, and reports `TEST PASSED`.
- ARM32 `arm32-virtio-fat32-smf` builds with the LLVM backend and reaches `spl_start()` under QEMU.
- ARM32 now finds the VirtIO block MMIO slot at `0x0A003E00`; serial trace reaches `VirtioBlkDriver.new` completion (`103`, `104`).

## Remaining Work
- Continue ARM32 VirtIO/VFS bring-up after trace `104`. The current run stalls before the VFS init path reports the next trace, so the next investigation point is driver initialization after probe/new.
- Remove temporary numeric `arm_fs_exec_trace` instrumentation after ARM32 reaches `TEST PASSED`.
- Re-run:
  - `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_OS_BUILD_TIMEOUT_MS=240000 bin/simple os test --scenario=arm64-virtio-fat32-smf`
  - `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_OS_BUILD_TIMEOUT_MS=240000 bin/simple os test --scenario=arm32-virtio-fat32-smf`
  - `bin/simple test test/unit/os/qemu_runner_spec.spl`
  - `bin/simple test test/unit/os/kernel/loader/executable_source_spec.spl`

## Notes
- ARM32 serial text output is unreliable in this path; use numeric C-side trace markers until the ABI/runtime issue is fixed.
- ARM32 LLVM currently shows suspicious behavior for some `u64` loops and large `u32` comparisons in early boot code. Keep early probing logic conservative until verified.
