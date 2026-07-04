<!-- codex-architecture -->

# System Test Plan: SimpleOS Game Compatibility Platform

Date: 2026-05-07

## Test Lanes

### ST-GAME-001: Linux Personality Smoke

Evidence:

- ELF64 user binary loads through `src/os/kernel/loader/`.
- `mmap`, `mprotect`, `futex`, `clone`, `signal`, `epoll`, `eventfd`, `timerfd`, and `signalfd` status rows exist.
- `/proc`, `/sys`, and `/dev` compatibility markers are emitted.

### ST-GAME-002: Native SDL/Vulkan Game Smoke

Evidence:

- SDL input and window path resolves through SimpleOS compositor/display services.
- Vulkan loader and ICD discovery status is emitted.
- Driver platform marker rejects framebuffer/BGA/VirtIO-GPU compute claims without evidence.

### ST-GAME-003: Audio And Input Smoke

Evidence:

- Intel HDA + Realtek HDA probe reaches `supported` only with controller, codec, DMA, period, and mixer.
- Keyboard and mouse event streams are observed.
- Steam Input/XInput lanes report `missing` until bridge implementation exists.

### ST-GAME-004: Steam Runtime Prefix Smoke

Evidence:

- `/games/app_<id>/root`, `compatdata/pfx`, `shadercache`, `saves`, `logs`, and `config.sdn` are created or reported.
- Runtime sandbox emits filesystem, network, IPC, process, and device policy markers.

### ST-GAME-005: Proton Host Readiness Smoke

Evidence:

- Proton readiness report includes Wine, DXVK, VKD3D-Proton, FAudio, Media Foundation, Steam API, overlay, and crash logs.
- If any required Linux ABI, Vulkan, audio, input, or prefix gate is missing, Proton status is blocked.

### ST-GAME-006: Porting Toolkit Report Smoke

Evidence:

- A synthetic game profile produces missing ABI, syscall, ioctl, shader, audio, input, and filesystem findings.
- Report separates observed evidence from inferred blockers.

## Initial Automated Tests

- `bin/simple test test/01_unit/os/drivers/driver_platform_contract_spec.spl --mode=interpreter`
- `bin/simple test test/01_unit/os/qemu_runner_spec.spl --mode=interpreter`

## Exit Criteria

The platform cannot claim SteamOS-level support until Linux personality, Vulkan/Mesa, audio, input, runtime prefix, and Proton host readiness all have fresh evidence.
