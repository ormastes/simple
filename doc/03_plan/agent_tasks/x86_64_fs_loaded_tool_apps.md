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

## Status

### Done

- `execve(path, argv, envp)` userspace forwarding is wired through SOSIX, libc, and the kernel image-builder path.
- `spawn_binary` now accepts copied `argv/envp` vectors in the kernel ABI instead of dropping them on syscall entry.
- x86_64 syscall fast-path and shim comments are aligned with the real syscall 13/59 argument contract.
- launcher and shell process-spawn surfaces already preserve argv via `posix_spawn_with_args(...)`.
- init service definitions can now carry `args`, and `InitService` forwards them into the launcher/default `spawn_binary_with_args(...)` path.
- focused regression coverage exists for:
  - userspace `execve` ABI forwarding
  - userspace spawn ABI forwarding
  - kernel syscall-13 argv/envp wiring
  - init-service argument forwarding

### Remaining

- Keep the broader behavior-level spawn argv/envp kernel spec green once the unrelated compiler failure blocking it is resolved.
- Repair the stale process-image builder spec so image-level argv/envp assertions are a reliable gate.
- Audit remaining production launchers for real env-aware spawn needs; argv is now wired, but envp is still mostly unused above the syscall surface.
- Replace staged `/usr/bin/clang`, `/usr/bin/lld`, `/usr/bin/rustc`, `/usr/bin/cargo` wrapper payloads with real filesystem-runnable SimpleOS executables.
- Convert `/sys/apps/llvm` and `/sys/apps/rust` from shell/runtime placeholders into real process-backed tool frontends.
- Preserve x86_64 as the first full runtime closure while keeping riscv64 packaging and FS-exec namespace parity honest.
- Enable in-guest `simple native-build` on the real filesystem-loaded tool path, then verify Stage2/Stage3 bootstrap convergence.

## Verification

- `bin/simple os test --scenario=x64-desktop-uefi`
- Required serial marker families:
  - `[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/<app> bytes=`
  - `[desktop-e2e] process-backed:ok app=<app> pid=`
  - existing WM/network desktop completion markers.
