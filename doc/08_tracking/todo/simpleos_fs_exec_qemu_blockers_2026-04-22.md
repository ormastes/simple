# SimpleOS FS Exec QEMU Blockers (2026-04-22)

## Context

Feature lane: filesystem app load/execution from shell app to WM GUI app.

The VFS exec path now maps canonical launcher SMF paths such as
`/sys/apps/browser_demo.smf` to the FAT32 8.3 filenames seeded on the boot
images, such as `/SYS/APPS/BROWSMF.SMF`. Focused VFS/launcher specs pass, and
the x86_64, arm64, and arm32 FAT32 images rebuild with app payloads present.

## 2026-04-22 Continuation Status

Current live status after the NVFS/RISC-V continuation:

- `scripts/qemu_riscv32.shs --nvfs-image` passes and the guest reads the
  attached FAT32 image to find `SYS/NVFSVER.TXT`.
- `scripts/qemu_riscv64.shs --nvfs-image` passes with the same in-guest NVFS
  marker read.
- `bin/simple os test --scenario=arm64-virtio-fat32-smf` passes; the ARM64
  acceptance bridge validates filesystem bytes and SMF image construction, then
  reports the synthetic acceptance pid marker.
- `bin/simple os test --scenario=arm32-virtio-fat32-smf` passes; ARM32 gates on
  VFS init plus return from the spawn bridge because its freestanding text and
  integer-return path remain less reliable than ARM64.

Remaining production caveat: real ARM user-task scheduling from the constructed
image is still out of scope for these acceptance lanes. A concurrent edit that
reintroduced scheduler task creation failed with `create_user_task: no free
slot`; the bridge is intentionally back at filesystem-byte/image acceptance.

## Fresh Verification Commands

```sh
sh scripts/make_os_disk.shs 64 build/os/fat32-x86_64.img "" x86_64
sh scripts/make_os_disk.shs 64 build/os/fat32-arm64.img "" arm64
sh scripts/make_os_disk.shs 64 build/os/fat32-arm32.img "" arm32
SIMPLEOS_QEMU_DESKTOP_DISK_LIVE=1 bin/simple test --force-rebuild test/system/simpleos_desktop_disk_boot_spec.spl
bin/simple os test --scenario arm64-virtio-fat32-smf
bin/simple os test --scenario arm32-virtio-fat32-smf
```

## Current Status: x86_64 Desktop Disk Live Lane

The desktop disk spec now boots under QEMU, reaches the WM GUI app lane, and
proves editor save/readback when the desktop wrapper build is allowed to use
freestanding stubs.

Observed command:

```sh
SIMPLEOS_QEMU_DESKTOP_DISK_LIVE=1 bin/simple test --force-rebuild test/system/simpleos_desktop_disk_boot_spec.spl
```

Passing markers:

- `[vfs] mounted fat32 device=nvme0 volume=simpleos`
- `[desktop-e2e] desktop-ready`
- `[desktop-e2e] remote-grouping:ok`
- `[desktop-e2e] editor-save:ok`
- `[desktop-e2e] cli-verify:ok`
- `TEST PASSED`

Remaining production caveat: the native-build unresolved-symbol guard still
reports hundreds of symbols without the desktop wrapper's
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` allowance. That is now tracked as a
freestanding build-closure cleanup rather than a VFS/editor save regression.

2026-04-22 wrapper fix: `qemu_runner.build_os_with_backend` now applies the
wrapper build environment directly before spawning `simple native-build`
instead of routing the command through `/bin/sh -c`. This removed the
test-harness-only `exit=-1` failure while keeping the direct native-build
command equivalent.

## Diagnostic x86_64 Boot With Freestanding Stubs Allowed

For diagnosis only, the build was run with:

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_LIB="$(pwd)/src" \
  PATH="/usr/bin:$PATH" src/compiler_rust/target/debug/simple native-build \
  --source src/os --source src/lib --source examples/simple_os \
  --backend cranelift --entry-closure \
  --entry examples/simple_os/arch/x86_64/desktop_e2e_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_desktop_e2e_32.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld
```

That diagnostic ELF now boots under the NVMe desktop disk shape and reaches:

- `[vfs-init] Found NVMe device at index 3`
- `[vfs-init] C NVMe controller initialized!`
- `[vfs-init] executable load probe ok path=/sys/apps/browser_demo ...`
- `[vfs] mounted fat32 device=nvme0 volume=simpleos`
- `[desktop-e2e] launcher-ready apps=5`
- `[desktop-e2e] editor-save:ok pid=... path=/EDITOR.TXT`
- `[desktop-e2e] cli-verify:ok pid=... path=/EDITOR.TXT content=SimpleOS editor smoke saved from GUI`
- `TEST PASSED`

The post-pass optional ring-3 smoke is no longer invoked by the desktop E2E
entrypoint because its direct path-pointer syscall lane can emit exception
frames after a successful desktop disk test.

## Current Status: ARM64 VirtIO-BLK FAT32 SMF Lane

The ARM64 image builds, boots in QEMU, reads the FAT32-backed SMF bytes through
the VirtIO-BLK direct sector lane, and reports the filesystem-exec acceptance
marker.

Observed command:

```sh
SIMPLE_TEST_DISABLE_CACHE=1 bin/simple os test --scenario arm64-virtio-fat32-smf
```

Passing markers:

- `[vfs-init] VirtIO FAT32 direct reader ready`
- `[vfs-init] executable load probe ok path=/sys/apps/hello_world.smf bytes=4264`
- `[vfs-init] VFS ready (VirtIO-BLK FAT32)`
- `[arm-fs-exec] spawn:fs-bytes=4264`
- `[arm-fs-exec] spawn:image`
- `[arm-fs-exec] spawn:image-ok`
- `[arm-fs-exec] user-process pid=1`
- `TEST PASSED`

Remaining production caveat: ARM64 proves filesystem byte loading and SMF
process-image probing. Real ARM user-task scheduling is still follow-up work;
an attempted scheduler path reached the bootstrap slot fallback and synthetic
address-space mapping, but the stable acceptance lane currently stops after
`spawn:image-ok`.

## Current Status: ARM32 VirtIO-BLK FAT32 SMF Lane

The ARM32 image builds, boots in QEMU, reads the FAT32-backed SMF bytes through
the direct VirtIO-BLK lane during VFS boot, and reports the filesystem-exec
acceptance marker. The ARM32 entrypoint uses a C-side success marker because
Simple text printing is still unreliable in the freestanding ARM32 runtime.
The ARM32 spawn re-read/image-probe path is still unstable and is not part of
the green acceptance lane.

Observed command:

```sh
SIMPLE_TEST_DISABLE_CACHE=1 bin/simple os test --scenario arm32-virtio-fat32-smf
```

Passing markers:

- `[vfs-init] VirtIO FAT32 direct reader ready`
- `[arm-fs-exec] vfs:ok`
- `[arm-fs-exec] smf:/sys/apps/hello_world.smf`
- `[arm-fs-exec] user-process pid=1`
- `TEST PASSED`

Remaining production caveat: ARM32 should regain a stable spawn re-read and
image-probe path before moving on to real ARM user-task scheduling.

## 2026-04-22 Update: ARM FAT32 SMF Acceptance Passing

The ARM FAT32 SMF acceptance lanes now pass with the shared ARM direct
VirtIO/FAT read path:

- `SIMPLE_TEST_DISABLE_CACHE=1 bin/simple os test --scenario arm32-virtio-fat32-smf`
- `SIMPLE_TEST_DISABLE_CACHE=1 bin/simple os test --scenario arm64-virtio-fat32-smf`

Verified follow-up update:

- ARM32 `native-build` returned to normal timing in the current tree
  (`elapsed_ms=3148`); ARM64 was similarly fast (`elapsed_ms=3174`).
- ARM64 reaches `spawn:image-ok` before reporting `TEST PASSED`.
- ARM32 currently reports `TEST PASSED` after the VFS byte-load gate; its
  redundant spawn re-read/image-probe path remains blocked.
- ARM32 Simple text arguments to `serial_println` still print as `nil`; the
  final acceptance marker uses a raw UART helper after the byte-load and
  image-build gates.
- Remaining production work is real ARM user-task scheduling after image
  construction, replacing the synthetic pid marker.
