# x86_64 FS-Loaded Tool Apps Plan

## Goal

Make the x86_64 SimpleOS desktop lane prove that tool-class apps are packaged on the FAT32 disk, resolved through `/sys/apps`, launched as process-backed apps, and joined to the WM.

## Scope

- Add filesystem app identities for:
  - `/sys/apps/simple_browser`
  - `/sys/apps/simple_compiler`
  - `/sys/apps/simple_interpreter`
  - `/sys/apps/simple_loader`
  - `/sys/apps/llvm`
  - `/sys/apps/rust`
- Package each app as disk media in `scripts/make_os_disk.shs`.
- Register each app in the launcher with deterministic Meta shortcuts.
- Extend the x86_64 desktop UEFI serial contract with VFS-read and process-backed markers for the new app set.

## Non-Goal

This pass does not port full LLVM or Rust compiler internals into ring-3 SimpleOS userland. It provides filesystem-loaded WM app shells and acceptance markers on the existing disk-backed process path, so later work can replace each shell payload with the real tool runtime without changing launcher, disk, or WM contracts.

## Verification

- `bin/simple os test --scenario=x64-desktop-uefi`
- Required serial marker families:
  - `[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/<app> bytes=`
  - `[desktop-e2e] process-backed:ok app=<app> pid=`
  - existing WM/network desktop completion markers.
