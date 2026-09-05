<!-- codex-architecture -->

# Feature Requirements: SimpleOS Game Compatibility Platform

Date: 2026-05-07

## Scope

SteamOS game support means making games believe they are running on a Linux gaming platform. SimpleOS must first host native Linux game ABI, graphics/audio/input/network/filesystem semantics, and Steam Runtime-style launch before Proton is a credible target.

## Requirements

### REQ-GAME-001: Game ABI Target Matrix

SimpleOS must publish a versioned game target matrix:

- Target A: native Linux x86_64 game, no Steam.
- Target B: native Linux Steam game.
- Target C: Windows game through Proton on x86_64.
- Target D: Proton plus CPU translation on non-x86.
- Target E: Simple-native game.

Acceptance:

- Each target has `missing`, `scaffold`, `partial`, `ready`, or `verified` status.
- Each status points at code paths and test evidence.
- Proton targets cannot be `ready` until Linux ABI and Vulkan/audio/input gates are at least `ready`.

### REQ-GAME-002: Linux Personality Foundation

SimpleOS must define a Linux personality under `src/os/linux_personality/`.

Acceptance:

- ELF64 loader handoff, dynamic linker handoff, mmap/mprotect, clone/thread, futex, signals, epoll/eventfd/timerfd/signalfd, ioctl routing, procfs, sysfs, devfs, and udev-like discovery have explicit contracts.
- Existing anchors in `src/os/kernel/loader/`, `src/os/libc/`, and `src/os/posix/` are referenced by readiness reports.
- Missing glibc ABI behavior is reported as a blocker, not treated as POSIX source compatibility.

### REQ-GAME-003: Vulkan/Mesa Game Graphics Platform

SimpleOS must expose a game graphics platform before Proton/DXVK work.

Acceptance:

- DRM/KMS-compatible display contracts, Vulkan loader, ICD discovery, Mesa host boundary, shader cache, and compositor handoff are represented.
- AMD, Intel, Qualcomm/ARM, RISC-V software Vulkan, and CPU fallback are represented by probe results.
- Framebuffer, BGA, and VirtIO-GPU may not claim compute acceleration without explicit evidence.

### REQ-GAME-004: Game Audio Platform

SimpleOS must provide a game audio compatibility surface.

Acceptance:

- Intel HDA controller and Realtek HDA codec are first concrete hardware targets.
- ALSA, PulseAudio, and PipeWire compatibility statuses are represented.
- DMA ring, period/timer, mixer, and CPU audio acceleration evidence are required before `ready`.

### REQ-GAME-005: Game Input Platform

SimpleOS must expose Linux game input semantics.

Acceptance:

- Keyboard, mouse, evdev, hidraw, udev discovery, SDL controller mapping, Steam Input bridge, XInput virtual device, and per-game virtual controller statuses are represented.
- Existing PS/2 input can satisfy only the first baseline, not Steam Input compatibility.

### REQ-GAME-006: Steam Runtime Container

SimpleOS must define a Steam Runtime-style launch root.

Acceptance:

- `/games/app_<id>/root`, `compatdata/pfx`, `shadercache`, `saves`, `logs`, and `config.sdn` are defined.
- Runtime launch includes filesystem, process, IPC, network, and device sandbox policy.
- Selected native Linux games run before Steam client or Proton readiness can be claimed.

### REQ-GAME-007: Proton Host Readiness

SimpleOS must host upstream Proton binaries rather than reimplementing Proton first.

Acceptance:

- Wine, DXVK, VKD3D-Proton, FAudio, Media Foundation, Steam API, overlay, and crash-log readiness are reported.
- 32-bit/i386 requirements are explicit blockers for older games.
- A Proton game cannot be accepted if Vulkan, audio, input, filesystem prefix, or Linux thread/signal/futex support is missing.

### REQ-GAME-008: Simple Game Porting Toolkit

SimpleOS must provide developer-facing game diagnostics.

Acceptance:

- `game_probe`, syscall trace, ioctl trace, Vulkan trace, shader trace, Proton prefix analyzer, missing ABI report, and compatibility DB are defined.
- Reports use SDN profiles and name missing features deterministically.
- Toolkit output distinguishes evidence from inference.
