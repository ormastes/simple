<!-- codex-architecture -->

# Agent Tasks: SimpleOS Game Compatibility Platform

Date: 2026-05-07

## Work Breakdown

### Task 1: Linux Personality Contracts

Owns:

- `src/os/linux_personality/abi/`
- `src/os/linux_personality/syscall/`
- readiness report for existing `src/os/kernel/loader/`, `src/os/libc/`, and `src/os/posix/` anchors.

Deliverable:

- Capability matrix and tests for ELF, dynlink, mmap/mprotect, futex, clone, signal, epoll, eventfd, timerfd, signalfd, ioctl, procfs, sysfs, and devfs.

### Task 2: Game Device Platform Contracts

Owns:

- `src/os/game/platform/`
- integration with `src/os/drivers/driver_platform_contract.spl`.

Deliverable:

- Graphics, audio, input, network, filesystem, and CPU fallback readiness markers.

### Task 3: Runtime Prefix And Sandbox

Owns:

- `src/os/game/runtime/`
- `/games/app_<id>/` SDN layout.

Deliverable:

- Prefix manifest parser and sandbox policy report.

### Task 4: Proton Host Readiness

Owns:

- `src/os/game/proton/`
- `src/os/game/steam/`.

Deliverable:

- Upstream Proton host readiness report with blockers for Wine, DXVK, VKD3D-Proton, FAudio, Media Foundation, Steam API, overlay, 32-bit userland, and crash logs.

### Task 5: Porting Toolkit

Owns:

- `src/os/game/porting_toolkit/`.

Deliverable:

- SDN compatibility DB, missing ABI report, trace report formats, and synthetic fixture tests.

## Coordination Rules

- Do not start Proton implementation before Linux personality and Vulkan/audio/input readiness markers exist.
- Do not claim GPU compute on framebuffer, BGA, or VirtIO-GPU without concrete compute runtime evidence.
- Keep Steam Runtime and Proton code above Linux personality facades; do not import syscall decoding internals directly.
- Add tests before promoting any status from `partial` to `ready`.
