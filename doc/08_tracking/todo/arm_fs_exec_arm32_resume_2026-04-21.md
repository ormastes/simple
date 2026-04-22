# ARM FS Exec ARM32 Resume - 2026-04-21

## Status
- 2026-04-22 continuation: ARM32 and ARM64 `*-virtio-fat32-smf` lanes both
  boot under QEMU and report `TEST PASSED` with bootstrap scheduler user-task
  registration enabled.
- ARM64 `arm64-virtio-fat32-smf` boots under QEMU, reads `/sys/apps/hello_world.smf` from FAT32, creates the user task, and reports `TEST PASSED`.
- ARM32 `arm32-virtio-fat32-smf` builds with the LLVM backend and reaches `spl_start()` under QEMU.
- ARM32 now finds the VirtIO block MMIO slot at `0x0A003E00`; serial trace reaches `VirtioBlkDriver.new` completion (`103`, `104`).

## Remaining Work
- ARM32 still keeps numeric trace markers because text output is sparse in the
  freestanding runtime, but the acceptance marker is gated on VFS init, SMF
  image construction, and bootstrap scheduler registration.
- Remove temporary numeric `arm_fs_exec_trace` instrumentation after the ARM32
  return-value issue is fixed; keeping it for now is intentional because ARM32
  Simple text output is still unreliable.
- Re-run:
  - `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_OS_BUILD_TIMEOUT_MS=240000 bin/simple os test --scenario=arm64-virtio-fat32-smf`
  - `SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_OS_BUILD_TIMEOUT_MS=240000 bin/simple os test --scenario=arm32-virtio-fat32-smf`
  - `bin/simple test test/unit/os/qemu_runner_spec.spl`
  - `bin/simple test test/unit/os/kernel/loader/executable_source_spec.spl`

## Notes
- ARM32 serial text output is unreliable in this path; use numeric C-side trace markers until the ABI/runtime issue is fixed.
- ARM32 LLVM currently shows suspicious behavior for some `u64` loops and large `u32` comparisons in early boot code. Keep early probing logic conservative until verified.
