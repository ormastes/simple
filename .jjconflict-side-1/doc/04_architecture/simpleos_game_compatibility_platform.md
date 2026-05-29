<!-- codex-architecture -->

# Architecture: SimpleOS Game Compatibility Platform

Date: 2026-05-07

## Decision

Build SteamOS game support as a Linux-compatible game platform above SimpleOS, not as per-game ports. The compatibility target is:

1. native Linux game ABI;
2. Steam Linux Runtime-style rootfs and launcher shape;
3. Proton/Wine hosting for Windows games;
4. Vulkan/Mesa/DRM, audio, input, network, and filesystem compatibility;
5. Simple-native game SDK and porting tools after the Linux/Proton path is credible.

This extends the existing Wine substrate in `doc/04_architecture/simpleos_wine_substrate.md`. Wine/Proton is not the first layer; it depends on Linux ABI, dynamic loader, graphics, audio, input, and container work being observable first.

## Current State Map

Existing anchors:

- ELF and process image loading: `src/os/kernel/loader/elf64.spl`, `src/os/kernel/loader/elf_loader.spl`, `src/os/kernel/loader/process_image.spl`, `src/os/kernel/loader/dylib_registry.spl`.
- Syscall and POSIX-like surface: `src/os/kernel/abi/syscall_shim.spl`, `src/os/posix/`, `src/os/libc/`.
- Thread and wait primitives: `src/os/libc/simpleos_pthread.c`, `src/os/libc/simpleos_epoll.c`, `src/os/libc/simpleos_eventfd.c`, `src/os/libc/simpleos_timerfd.c`, `src/os/libc/simpleos_signalfd.c`.
- Device and exokernel driver direction: `src/os/drivers/driver_platform_contract.spl`, `src/os/services/driver_supervisor/supervisor.spl`, `src/os/services/pcimgr/pcimgr.spl`.
- Graphics and compositor: `src/os/drivers/gpu/`, `src/os/drivers/virtio/virtio_gpu.spl`, `src/os/compositor/`, `src/os/services/display/`, `src/os/services/wm/`.
- Input: `src/os/drivers/input/ps2_keyboard.spl`, `src/os/drivers/input/ps2_mouse.spl`, `src/os/gui/input_event.spl`.
- Networking: `src/os/services/netstack/`, `src/os/posix/socket_compat.spl`.
- Package/prefix groundwork: `src/os/tools/pkg/`, `src/os/packages/os_packages.spl`, `src/os/services/vfs/`.

Gaps:

- No versioned Linux personality module yet.
- No glibc ABI contract; `src/os/libc` is a SimpleOS libc surface.
- No Steam Runtime rootfs/container launcher contract.
- No DRM/KMS ioctl, Vulkan loader, Mesa ICD, Wayland/XWayland, or Gamescope-like compositor contract.
- No ALSA/PulseAudio/PipeWire shims.
- No udev/evdev/hidraw discovery contract beyond PS/2 input.
- No Proton prefix manager, compatibility DB, shader cache, or per-game profile.

## Layer List

### Layer 0: SimpleOS Kernel And Services

Owns scheduling, VM, capabilities, IPC, VFS, networking, display, driver supervision, and process lifecycle.

Public to next layer:

- Process, thread, VM, fd, socket, timer, signal, and filesystem calls through `src/os/kernel/abi/`, `src/os/posix/`, and `src/os/libc/`.
- Device broker and hardware capabilities through `src/os/services/driver_supervisor/`, `src/os/services/pcimgr/`, and `src/os/drivers/driver_platform_contract.spl`.

### Layer 1: Linux Personality

Proposed path: `src/os/linux_personality/`.

Owns Linux-compatible ABI contracts:

- ELF64 and dynamic linker handoff;
- mmap/munmap/mprotect, fixed mappings, JIT executable memory;
- clone, futex, pthread, TLS, robust lists;
- epoll, eventfd, timerfd, signalfd, poll/select;
- signals and crash handler semantics;
- ioctl routing;
- `/proc`, `/sys`, `/dev`, udev-like discovery;
- filesystem semantics: symlinks, mmap files, locks, large files, casefold prefix support;
- optional 32-bit/i386 lane after x86_64 is stable.

Tree-private rule: Linux syscall decoding and Linux errno/flag translation stay under `linux_personality/syscall/` and are not imported directly by Steam or Proton code.

### Layer 2: Game Device Platform

Proposed path: `src/os/game/platform/`.

Owns game-facing device contracts:

- DRM/KMS-like display manager and ioctl bridge;
- Vulkan loader and ICD discovery;
- Mesa hosting boundary for AMD, Intel, Qualcomm/ARM, software Vulkan, and later vendor stacks;
- CPU fallback kernels for pixels, shaders, and audio using SIMD evidence from `driver_platform_contract.spl`;
- ALSA, PulseAudio, and PipeWire compatibility endpoints;
- evdev, hidraw, SDL controller DB, Steam Input bridge, and virtual XInput device;
- BSD socket/TLS/cert-store game network profile.

### Layer 3: Game Runtime Containers

Proposed path: `src/os/game/runtime/`.

Owns Steam Runtime-style launch:

- rootfs/container namespace;
- game prefix layout under `/games/app_<id>/`;
- per-game mount table, save path, shader cache, logs, and compatdata;
- process, filesystem, network, IPC, device, and GPU capability sandbox;
- launch manifests in SDN.

### Layer 4: Steam And Proton Host

Proposed paths: `src/os/game/steam/` and `src/os/game/proton/`.

Owns:

- Steam client or steamcmd bootstrap contract;
- Steam Runtime environment variables and dependency discovery;
- Proton/Wine host validation;
- DXVK and VKD3D-Proton Vulkan requirement reporting;
- FAudio and Media Foundation host checks;
- Steam overlay, crash logs, and compatibility DB integration.

Rule: host upstream Proton binaries before reimplementing Proton components.

### Layer 5: Simple Game Porting Toolkit

Proposed path: `src/os/game/porting_toolkit/`.

Owns:

- `game_probe`, syscall trace, ioctl trace, Vulkan trace, shader trace;
- Proton prefix analyzer;
- missing ABI reports;
- SDN compatibility database and auto-patch rule format;
- Simple shader IR conversion reports for future SimpleGPU work.

## MDSOC Visibility Matrix

| Raw layer | Common tree node | Public to parent node | Public to next-layer sibling |
| --- | --- | --- | --- |
| `src/os/linux_personality/syscall/` | `src/os/linux_personality/abi/` | Linux flags, errno, syscall IDs, structs | syscall dispatch facade only |
| `src/os/game/platform/gfx/` | `src/os/game/platform/common/` | device capability records, Vulkan/DRM status | compositor and runtime receive status, not driver internals |
| `src/os/game/platform/audio/` | `src/os/game/platform/common/` | audio device, period, DMA, backend status | runtime receives ALSA/Pulse/PipeWire endpoint facade |
| `src/os/game/platform/input/` | `src/os/game/platform/common/` | evdev/hidraw/controller records | Steam and Proton receive virtual controller facade |
| `src/os/game/runtime/` | `src/os/game/common/` | prefix, app ID, sandbox, launch profile | Steam and Proton use runtime launcher facade |
| `src/os/game/proton/` | `src/os/game/common/` | Proton profile, DXVK/VKD3D/FAudio status | porting toolkit reads reports only |

## Success Gates

1. Run BusyBox-like ELF and SDL sample through Linux personality.
2. Run Vulkan info or `vkcube` equivalent through Vulkan/Mesa/DRM compatibility.
3. Run one native Linux game outside Steam.
4. Run Steam Runtime-style rootfs with a native Linux game.
5. Run a small Windows DirectX 9 sample through Proton/DXVK.
6. Produce a Simple Game Porting Toolkit report that names missing ABI/device features instead of hiding failures.

## Migration Sequence

1. Add `src/os/linux_personality/abi/` capability records and tests backed by current loader/libc/posix files.
2. Add `src/os/game/platform/` contracts for graphics, audio, input, network, filesystem, and CPU fallback.
3. Wire driver evidence from `src/os/drivers/driver_platform_contract.spl` into game platform readiness markers.
4. Add runtime prefix and container manifest parsing before Steam client work.
5. Add Proton host readiness checks after native Linux game gates pass.
6. Add porting toolkit reports and SDN compatibility profiles.
