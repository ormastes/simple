# SStack State: simpleos-game-compat-platform

## User Request
> next task from the plan — simpleos_game_compatibility_platform (5 tasks: Linux Personality, Game Device, Runtime Sandbox, Proton Host, Porting Toolkit)

## Task Type
feature

## Refined Goal
> Implement SimpleOS game compatibility platform: Linux personality ABI contracts (ELF/syscall/clone/signal/epoll), game device platform contracts (graphics/audio/input/network/fs/CPU readiness), runtime prefix + sandbox policy, Proton/Steam host readiness reporting, and porting toolkit with compatibility DB and trace reports.

## Acceptance Criteria
- [ ] AC-1: Linux personality syscall contract — capability matrix for ELF, dynlink, mmap/mprotect, futex, clone, signal, epoll/eventfd/timerfd/signalfd, ioctl
- [ ] AC-2: Linux personality procfs/sysfs/devfs — virtual filesystem stubs with readiness markers
- [ ] AC-3: Game device graphics readiness — ties to GPU vendor probes from driver platform, reports Vulkan/compute availability
- [ ] AC-4: Game device audio/input/network/fs readiness — markers for HDA, HID, network stack, filesystem access
- [ ] AC-5: Game device CPU fallback — x86_64/ARM/RISC-V capability checks with SIMD tier markers
- [ ] AC-6: Runtime prefix manifest — SDN prefix parser with app_id, install path, library overrides, env vars
- [ ] AC-7: Sandbox policy report — capability grants (network/fs/ipc/gpu) with deny-by-default enforcement
- [ ] AC-8: Proton host readiness — blockers for Wine, DXVK, VKD3D-Proton, FAudio, Media Foundation, Steam API, overlay
- [ ] AC-9: Proton 32-bit userland + crash log — multilib readiness and crash log collection contract
- [ ] AC-10: Porting toolkit — SDN compatibility DB format, missing ABI report, trace report format, synthetic fixture tests

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 5 tasks. 5 parallel agents (A-E). Plan at doc/03_plan/agent_tasks/simpleos_game_compatibility_platform.md. Existing: kernel/loader (ELF, dynlib), posix/ (fd, pipe, errno, dynlib), game/ (platform contract, steam support), libc/ (cxxabi).

### 5-implement
<pending>
