# SStack State: simpleos-game-compat-platform

## User Request
> next task from the plan — simpleos_game_compatibility_platform (5 tasks: Linux Personality, Game Device, Runtime Sandbox, Proton Host, Porting Toolkit)

## Task Type
feature

## Refined Goal
> Implement SimpleOS game compatibility platform: Linux personality ABI contracts (ELF/syscall/clone/signal/epoll), game device platform contracts (graphics/audio/input/network/fs/CPU readiness), runtime prefix + sandbox policy, Proton/Steam host readiness reporting, and porting toolkit with compatibility DB and trace reports.

## Acceptance Criteria
- [x] AC-1: Linux personality syscall contract — capability matrix for ELF, dynlink, mmap/mprotect, futex, clone, signal, epoll/eventfd/timerfd/signalfd, ioctl
- [x] AC-2: Linux personality procfs/sysfs/devfs — virtual filesystem stubs with readiness markers
- [x] AC-3: Game device graphics readiness — ties to GPU vendor probes from driver platform, reports Vulkan/compute availability
- [x] AC-4: Game device audio/input/network/fs readiness — markers for HDA, HID, network stack, filesystem access
- [x] AC-5: Game device CPU fallback — x86_64/ARM/RISC-V capability checks with SIMD tier markers
- [x] AC-6: Runtime prefix manifest — SDN prefix parser with app_id, install path, library overrides, env vars
- [x] AC-7: Sandbox policy report — capability grants (network/fs/ipc/gpu) with deny-by-default enforcement
- [x] AC-8: Proton host readiness — blockers for Wine, DXVK, VKD3D-Proton, FAudio, Media Foundation, Steam API, overlay
- [x] AC-9: Proton 32-bit userland + crash log — multilib readiness and crash log collection contract
- [x] AC-10: Porting toolkit — SDN compatibility DB format, missing ABI report, trace report format, synthetic fixture tests

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-17
- [x] 6-refactor (Tech Lead) — 2026-05-17
- [x] 7-verify (QA) — 2026-05-17
- [x] 8-ship (Release Mgr) — 2026-05-17

## Phase Outputs

### 1-dev
10 ACs across 5 tasks. 5 parallel agents (A-E). Plan at doc/03_plan/agent_tasks/simpleos_game_compatibility_platform.md. Existing: kernel/loader (ELF, dynlib), posix/ (fd, pipe, errno, dynlib), game/ (platform contract, steam support), libc/ (cxxabi).

### 5-implement
5 parallel Sonnet agents. 7 files created:
- src/os/linux_personality/syscall_contract.spl (305 lines) — SyscallCapability + LinuxSyscallMatrix + LinuxPersonalityContract
- src/os/linux_personality/vfs_stubs.spl (209 lines) — ProcfsEntry + VfsStubRegistry + LinuxVfsContract
- src/os/game/platform/device_readiness.spl (286 lines) — GPU/Audio/Input/Network/Fs/Cpu readiness + aggregate report
- src/os/game/runtime/prefix_sandbox.spl (~300 lines) — PrefixManifest + SandboxCapability + SandboxPolicy + SandboxEnforcer
- src/os/game/proton/host_readiness.spl (288 lines) — ProtonComponent + ProtonHostReport + MultilibReadiness + CrashLogContract + ProtonPlatformGate
- src/os/game/porting_toolkit/compat_toolkit.spl — CompatEntry + CompatDatabase + MissingAbiReport + TraceReport + PortingFixture + PortingToolkitReport
- test/unit/os/game_compat_spec.spl — 18 tests
### 7-verify
18/18 tests PASS. Commit d246b0b1b5 pushed to origin/main.
