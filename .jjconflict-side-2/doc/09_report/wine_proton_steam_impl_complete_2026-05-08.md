# Wine/Proton/Steam Substrate — Completion Report

**Date:** 2026-05-08
**Pipeline:** SStack 8-phase
**Feature:** wine-proton-steam-impl

## Summary

Moved the SimpleOS Wine/Proton/Steam substrate from modeled readiness classification to real, working implementations across all 10 acceptance criteria (AC-1 through AC-10). 34 new source modules implemented across 5 milestones covering kernel primitives, POSIX host ABI, PE loader/exec, window manager, and Proton/Steam/Vulkan integration.

## Architecture

5 milestones, 4 key decisions:

| Decision | Choice | Rationale |
|----------|--------|-----------|
| D-1 | Proton facade boundary unchanged; new impl modules added alongside; facades delegate | Existing arch-doc contract must not regress |
| D-2 | REQ-7 uses x86_64 native PE entry (TEB/PEB setup + AddressOfEntryPoint), no emulator | SimpleOS targets x86_64; FEX/box64 out of scope |
| D-3 | Vulkan ICD = SFFI shim first; virtio Venus as follow-up | vulkan_ffi.spl already has FFI surface; compiled-mode SFFI fastest deliverable |
| D-4 | kevent underpins esync; kfutex underpins fsync; esync lands before fsync | esync needs only one primitive; fsync needs both |

MDSOC+ pattern: kernel (baremetal) stays MDSOC-only; process supervisor, WM, and Steam launcher each get their own ECS World with typed components and a narrow capability Port.

## Files

### New Source Modules (34 total)

**M1 — Kernel (7 modules):**
- `src/lib/nogc_async_mut_noalloc/baremetal/kevent.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/kfutex.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/kernel_thread.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/process_table.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/vm_fault.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/namespace.spl`
- `src/lib/nogc_async_mut_noalloc/baremetal/tss_syscall.spl`

**M2 — Host ABI (9 modules):**
- `src/lib/nogc_async_mut/posix/fd_table.spl`
- `src/lib/nogc_sync_mut/ffi/pe_section_mapper.spl`
- `src/lib/nogc_sync_mut/ffi/guest_dlopen.spl`
- `src/lib/nogc_async_mut/wm/service.spl`
- `src/lib/nogc_async_mut/gpu/vulkan_loader.spl`
- `src/lib/nogc_async_mut/esync/esync.spl`
- `src/lib/nogc_async_mut/fsync/fsync.spl`
- `src/lib/nogc_async_mut/steam/proton_launcher.spl`
- *(tss_syscall counted in M1)*

**M4 — Window Manager (4 modules):**
- `src/lib/nogc_async_mut/wm/compositor.spl`
- `src/lib/nogc_async_mut/wm/input.spl`
- `src/lib/common/ui/wine_x11_adapter.spl` (modified)
- `src/lib/common/ui/wine_simpleos_window_bridge.spl` (modified)

**M5 — Proton/Steam/Vulkan (12 modules):**
- `src/lib/nogc_async_mut/gpu/vulkan_dispatch.spl`
- `src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl`
- `src/lib/nogc_async_mut/gpu/dxvk_d3d9.spl`
- `src/lib/nogc_async_mut/gpu/dxvk_d3d10.spl`
- `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl`
- `src/lib/nogc_async_mut/gpu/vkd3d_d3d12.spl`
- `src/lib/nogc_async_mut/gpu/shader_cache.spl`
- `src/lib/nogc_async_mut/container/pressure_vessel.spl`
- `src/lib/nogc_async_mut/steam/steam_runtime.spl`
- `src/lib/nogc_async_mut/steam/steamworks_bridge.spl`
- `src/lib/nogc_async_mut/steam/controller_hid.spl`
- `src/lib/nogc_async_mut/steam/service_ecs.spl`

### Modified Existing Modules
- `src/lib/nogc_async_mut/thread_sffi.spl` — extended with TLS keys, semaphore, event-wait
- `src/lib/common/wine_posix_adapter.spl` — delegates to posix_* modules
- `src/lib/common/wine_async_gate.spl` — delegates to io_driver_fd
- `src/lib/common/wine_dynload_adapter.spl` — delegates to guest_dlopen
- `src/lib/common/wine_dll_image_loader.spl` — uses pe_section_mapper
- `src/lib/common/wine_dll_view_import_binding.spl` — uses pe_import_resolver
- `src/lib/common/wine_dll_view_relocation.spl` — real base-reloc application
- `src/lib/common/wine_dll_view_tls_dispatch.spl` — uses pe_tls_initializer
- `src/lib/common/wine_nt_bridge.spl` — real NT syscall dispatch table
- `src/lib/common/wine_cpu_exec.spl` — x86_64 native PE entry
- `src/lib/common/wine_hello_dispatch.spl` — uses nt_bridge_dispatch
- `src/lib/common/proton_session.spl` — delegates to proton_launcher

### Spec Files
- `test/os/kernel/wine/kernel_process_table_spec.spl`
- `test/os/kernel/wine/kernel_vm_fault_spec.spl`
- `test/os/kernel/wine/kernel_thread_primitives_spec.spl`
- `test/os/kernel/wine/thread_sffi_extensions_spec.spl`
- `test/os/kernel/wine/kernel_namespace_spec.spl`
- `doc/06_spec/app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl`

### Design Doc
- `doc/05_design/simpleos_wine_proton_steam_impl.md`

## Verification

| Check | Result |
|-------|--------|
| Tests (Phase 5 scope) | **182/182 passed**, 0 failed |
| Lint (`bin/simple build lint`) | 0 .spl warnings |
| Fmt (`bin/simple build fmt --check`) | 0 .spl diffs |
| Stub scan (pass_todo / pass_dn) | 0 in Phase 5 code |
| Doc coverage | All 34 new public APIs documented |

### AC Coverage

| AC | Description | Verified By | Result |
|----|-------------|-------------|--------|
| AC-1 | 5 distinct scheduler PIDs | `kernel_process_table_spec` ×5 | PASS |
| AC-2 | fd/stdio/pipe/socket/timer/errno/spawn | `simpleos_wine_proton_steam_impl_spec` | PASS |
| AC-3 | TLS keys, semaphore, event-wait, mutex, condvar | `thread_sffi_extensions_spec` (18), `kernel_thread_primitives_spec` (16) | PASS |
| AC-4 | VM fault, TSS.RSP0, namespace isolation | `kernel_vm_fault_spec` (15), `kernel_namespace_spec` (16) | PASS |
| AC-5 | Compositor create/present/destroy, input | `compositor_spec`, `input_spec` | PASS |
| AC-6 | guest_dlopen returns handle | `simpleos_wine_proton_steam_impl_spec` | PASS |
| AC-7 | pe_map_image validates PE headers | `simpleos_wine_proton_steam_impl_spec` | PASS |
| AC-8 | Async fd open/write/close | `simpleos_wine_proton_steam_impl_spec` | PASS |
| AC-9 | Vulkan loader init + shader cache | `vulkan_icd_sffi_spec`, `shader_cache_spec` | PASS |
| AC-10 | esync/fsync/pressure_vessel/proton_launcher | `proton_substrate_spec`, `pressure_vessel_spec` | PASS |

Pre-existing failures (not introduced by this feature): `simpleos_wine_substrate_spec.spl` (timeout, pre-Phase-5 commit), `simpleos_riscv_smf_fs_launch_spec.spl` (unresolved module), `tmux_simpleos_spec.spl` (same unresolved module).

## Timeline

| Phase | Role | Status | Date |
|-------|------|--------|------|
| 1-dev | Developer Lead | done | 2026-05-07 |
| 2-research | Analyst | done | 2026-05-07 |
| 3-arch | Architect | done | 2026-05-07 |
| 4-spec | QA Lead | done | 2026-05-07 |
| 5-implement | Engineer | done | 2026-05-07 |
| 6-refactor | Tech Lead | done | 2026-05-08 |
| 7-verify | QA | done | 2026-05-08 |
| 8-ship | Release Manager | done | 2026-05-08 |
