# Completion Audit: SimpleOS Wine Substrate

Date: 2026-05-06

## Objective Restated

Deliver the production-quality prerequisites for a controlled SimpleOS Wine path:

1. research Wine-needed SimpleOS and Simple lib features;
2. provide Wine-facing WM/graphics prerequisites with SimpleOS-backed evidence;
3. provide Wine-facing process/container/VM prerequisites with OS-backed evidence;
4. keep broad POSIX/thread/dynload/service prerequisites explicit;
5. run a controlled non-GUI `hello.exe`;
6. keep unsupported Wine/PE behavior blocked with structured errors.

## Prompt-To-Artifact Checklist

| Requirement | Evidence | Status |
| --- | --- | --- |
| Wine research | `doc/01_research/local/simpleos_wine_support.md`, `doc/01_research/domain/simpleos_wine_support.md`, `doc/09_report/simpleos_wine_support_research_2026-05-06.md` | Done |
| Requirements/design/test artifacts | `doc/02_requirements/feature/simpleos_wine_substrate.md`, `doc/02_requirements/nfr/simpleos_wine_substrate.md`, `doc/04_architecture/simpleos_wine_substrate.md`, `doc/04_architecture/simpleos_wine_wm_vm.md`, `doc/05_design/simpleos_wine_substrate.md`, `doc/03_plan/sys_test/simpleos_wine_substrate.md`, `doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl` | Done |
| SimpleOS executable environment gate | `src/lib/common/wine_simpleos_exec_env_gate.spl` requires QEMU VM, full OS boot, kernel syscall ABI, scheduler and VFS service evidence, user process, VM space, filesystem, window system, network, separate pid/fs/ipc/net/capability container namespace facets, container rootfs evidence, and NVFS rootfs backend evidence; `src/lib/common/wine_substrate.spl` exposes this as the `exec_env` matrix row/gate | Implemented prerequisite |
| Dynamic loading prerequisite | `src/lib/common/wine_dynload_adapter.spl` requires native loader APIs, search path/dependency/namespace coverage, relocation/import/TLS surfaces, structured loader errors, and bounded NTDLL `LdrLoadDll`/`LdrGetProcedureAddress`/`LdrUnloadDll` evidence before dynload readiness | Implemented prerequisite |
| Registry prerequisite | `src/lib/common/wine_advapi32_registry.spl` and `src/lib/common/wine_ntdll_registry.spl` provide bounded create/open/set/query/close registry evidence; `src/lib/common/wine_substrate.spl` exposes this as the `registry` matrix row/gate | Implemented prerequisite |
| Thread/TLS/wait prerequisite | `src/lib/common/wine_thread_adapter.spl` requires thread/TLS/synchronization/wait/fault APIs and bounded NT `CreateThread`/`WaitForSingleObject` evidence before pthread readiness | Implemented prerequisite |
| POSIX/file-I/O prerequisite | `src/lib/common/wine_posix_adapter.spl` requires fd/process/stdio/wait/timer/socket/path/errno APIs over `nogc_async_mut`, and bounded KERNEL32 `CreateFileW`/`ReadFile`/`GetFileType`/`CloseHandle` evidence before POSIX readiness | Implemented prerequisite |
| Service and peripheral prerequisite | `src/lib/common/wine_service_adapter.spl` requires complete IPC, handle, audio, font, crypto, HID, printing, and multimedia service declarations plus bounded ADVAPI32 `OpenSCManagerW`/`CreateServiceW`/`OpenServiceW`/`StartServiceW`/`CloseServiceHandle` evidence before service readiness; audio, font, and input rows require separate waveOut/font/HID evidence gates instead of broad `host=verified` evidence | Implemented prerequisite |
| WM/graphics production prerequisite | `src/lib/common/ui/wine_simpleos_window_bridge.spl` creates SimpleOS `/win` `WindowRecord` state, framebuffer present evidence, cursor evidence, and clipboard evidence; `src/lib/common/ui/wine_x11_adapter.spl` requires that bridge through `wine_x11_backend_production_ready` | Implemented prerequisite |
| USER32/GDI32 GUI prerequisite | `src/lib/common/wine_user32_window.spl` and `src/lib/common/wine_gdi32_drawing.spl` provide bounded USER32 window lifecycle/message-loop evidence and GDI32 text blit evidence; `src/lib/common/wine_substrate.spl` exposes these as `user32` and `gdi32` matrix rows/gates | Implemented prerequisite |
| KERNEL32 core prerequisite | `src/lib/common/wine_nt_api_catalog.spl` and KERNEL32 bridge specs cover bounded virtual memory, heap, TLS/FLS, sync events, error state, atom table, time/version, startup info, and interlocked evidence; `src/lib/common/wine_substrate.spl` exposes this as the `kernel32_core` matrix row/gate | Implemented prerequisite |
| VM/container production prerequisite | `src/lib/common/wine_vm_adapter.spl` distinguishes modeled spaces from OS process/address-space/container-backed spaces; `src/lib/common/wine_image_vm_map.spl` maps validated PE images plus stack/guard before execution | Implemented prerequisite |
| PE/COFF and CPU preparation | `src/lib/common/wine_pe_gate.spl`, `src/lib/common/pe_coff_header.spl`, `src/lib/common/wine_pe_loader_runtime.spl`, `src/lib/common/wine_image_map.spl`, `src/lib/common/wine_x86_64_decode.spl`, and `src/lib/common/wine_cpu_exec.spl` validate image layout, entry windows, imports, relocation/TLS readiness, decoded call targets, safe prologues, and dispatch evidence before controlled execution | Verified for controlled hello path |
| NT bridge and dispatch sequence | `src/lib/common/wine_nt_bridge.spl` and `src/lib/common/wine_hello_dispatch.spl` execute only the decoded-plan `GetStdHandle`, `WriteFile`, `ExitProcess` sequence with stdout handle, byte-count, payload RVA, and exit-code evidence | Verified for controlled hello path |
| Known non-GUI `hello.exe` command | `src/app/wine_hello/main.spl` prints `Hello from SimpleOS Wine` through OS-backed VM image mapping, composed manifest, PE validation, import binding, CPU plan, NT bridge, and decoded stdout payload path | Verified |
| Controlled GUI hello milestone | `src/lib/common/wine_gui_hello.spl` and `src/app/wine_gui_hello/main.spl` require the VM-backed PE hello path, then bind Wine-facing X11 state to SimpleOS `/win` framebuffer evidence before reporting window title/text/checksum | Verified |
| Unsupported programs stay blocked | Tests cover malformed PE, missing gates, unsupported imports, import/CPU target mismatch, missing stdout payload, missing decoder/dispatch evidence, reordered/missing/extra bridge calls, and unsupported/truncated x86_64 instructions | Verified for listed blockers |
| Full Wine readiness boundary | `src/lib/common/wine_substrate.spl` exposes `wine_substrate_full_wine_gate`, which requires every tracked substrate row and remains separate from the controlled `hello.exe` gate | Implemented boundary |
| Stub scan | Wine-scope source/test scan for stub markers returned no matches | Done |

## Verification Evidence

- `bin/simple check` on 16 impacted Wine files: all checks passed.
- `bin/simple test test/lib/common/ui/wine_simpleos_window_bridge_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/ui/wine_x11_adapter_spec.spl --mode=interpreter --clean`: 8 examples, 0 failures.
- `bin/simple test test/lib/common/wine_vm_adapter_spec.spl --mode=interpreter --clean`: 8 examples, 0 failures.
- `bin/simple test test/lib/common/wine_image_vm_map_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple test test/lib/common/wine_hello_exe_spec.spl --mode=interpreter --clean`: 18 examples, 0 failures.
- `bin/simple test test/integration/app/wine_hello_command_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple test test/lib/common/wine_gui_hello_spec.spl --mode=interpreter --clean`: 2 examples, 0 failures.
- `bin/simple test test/integration/app/wine_gui_hello_command_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- Wine-scope source/test stub scan: pass.

## 2026-05-07 Execution-Metadata Update

The controlled non-GUI hello path now carries decoded x86_64 sequence metadata from `wine_x86_64_decode.spl` into `WineCpuHelloExecutionPlan` and dispatches stdout execution through the plan's call sequence/count rather than reconstructing a local fixed sequence in `wine_hello_dispatch.spl`.

Fresh evidence:

- `bin/simple check` on 8 impacted source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_x86_64_decode_spec.spl`: 14 examples, 0 failures.
- `bin/simple test test/lib/common/wine_cpu_exec_spec.spl`: 16 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_bridge_spec.spl`: 14 examples, 0 failures.
- `bin/simple test test/lib/common/wine_hello_dispatch_spec.spl`: 11 examples, 0 failures.
- `bin/simple test test/lib/common/wine_hello_exe_spec.spl`: 13 examples, 0 failures.
- `bin/simple test test/integration/app/wine_hello_command_spec.spl`: 1 example, 0 failures.
- Wine-scope changed-file stub scan: pass.

Conservative boundary: this remains a controlled hello-path executor, not a general x86_64 CPU, arbitrary PE loader, or full Wine NT/Win32 dispatcher.

## 2026-05-07 x86_64 Frame-Prologue Decode Update

The bounded x86_64 decoder now recognizes frame-pointer prologue and epilogue
forms (`push rbp`, `mov rbp,rsp`, `pop rbp`) as structured scan-only evidence.
The known-console hello skeleton can be accepted after `push rbp; mov rbp,rsp;
sub rsp,imm8` without treating other REX MOV encodings as supported.

Fresh evidence:

- `bin/simple check` on x86_64 decoder source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_x86_64_decode_spec.spl --mode=interpreter --clean`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple check` on generated matcher specs: all checks passed.
- `bin/simple check src/lib`: 2706 files, all checks passed.

Conservative boundary: this is still scan and planning evidence only. It does
not add arbitrary x86_64 execution, broad REX MOV support, stack-frame mutation
semantics, or host CPU execution.

## 2026-05-07 x86_64 Wide Stack-Prologue Decode Update

The bounded x86_64 decoder now recognizes common imm32 stack allocation and
release forms (`sub rsp,imm32`, `add rsp,imm32`) as structured scan-only
evidence. The known-console hello skeleton can be accepted after a frame
prologue that uses wider stack allocation without treating other REX ALU forms
as supported.

Fresh evidence:

- `bin/simple check src/lib/common/wine_x86_64_decode.spl test/lib/common/wine_x86_64_decode_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl` passed.
- `bin/simple test test/lib/common/wine_x86_64_decode_spec.spl --mode=interpreter --clean`: 19 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_x86_64_frame_prologue_spec.spl --mode=interpreter --clean`: 2 examples, 0 failures.
- `bin/simple check` on generated matcher specs: all checks passed.
- `bin/simple check src/lib`: 2707 files, all checks passed.

Conservative boundary: this is still scan and planning evidence only. It does
not add arbitrary x86_64 execution, stack-frame mutation semantics, broad REX
ALU support, or host CPU execution.

## 2026-05-07 DLL Search-Order Modeling Update

The KERNEL32 module-loader layer now models a basename-only DLL search order before any real module-load behavior can be widened. It records KnownDlls, application directory, Windows system directories, current directory, and PATH-derived candidate paths while explicitly blocking host filesystem reads, real DLL loading, DLL entrypoint execution, and arbitrary PE execution.

Fresh evidence:

- `bin/simple check` on changed DLL-search source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_kernel32_module_loader_spec.spl`: 7 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_search_order_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2693 files, all checks passed.
- Wine DLL-search changed-file stub scan: pass.

## 2026-05-07 DLL Image-Map Handoff Update

The DLL image-loader handoff now composes modeled DLL search order with SimpleOS VM process-space map/unmap evidence while recording the modeled `NtCreateSection`/`NtMapViewOfSection`/`NtUnmapViewOfSection` lifecycle. It records a selected DLL path, mapped base, mapped size, and section handle while keeping host DLL file reads, persistent real DLL loading, DllMain, TLS callbacks, and arbitrary PE execution blocked.

Fresh evidence:

- `bin/simple check` on changed DLL image-map source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_image_loader_spec.spl`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_image_map_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2694 files, all checks passed.
- Wine DLL image-map changed-file stub scan: pass.

## 2026-05-07 DLL Load-Session State Update

The DLL load-session layer now records modeled loaded-image state on top of the DLL image-map handoff. It tracks selected path, mapped base/size, section handle, refcounted repeated loads, unloads, and rollback evidence while still blocking host DLL filesystem reads, persistent real DLL loading, DllMain, TLS callbacks, and arbitrary PE execution.

Fresh evidence:

- `bin/simple check` on changed DLL load-session source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_load_session_spec.spl`: 4 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_load_session_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2695 files, all checks passed.
- Wine DLL load-session changed-file stub scan: pass.

## 2026-05-07 DLL Entrypoint Lifecycle Gate Update

The DLL entrypoint lifecycle gate now requires modeled loaded-image evidence before recording loader-lock, TLS-before-DllMain, and process-attach ordering. Actual DllMain/TLS execution remains hard-blocked and reports `dll-entrypoint-execution-not-implemented` when requested.

Fresh evidence:

- `bin/simple check` on changed DLL entrypoint lifecycle source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_entrypoint_lifecycle_spec.spl`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_entrypoint_lifecycle_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2696 files, all checks passed.
- Wine DLL entrypoint lifecycle changed-file stub scan: pass.

## 2026-05-07 DLL File-Bytes Validation Update

The DLL file-bytes gate now validates supplied bytes for a selected DLL path before any real persistent mapping is allowed. It checks MZ/PE signatures, x86_64 PE32+ headers, the PE DLL characteristic, image size, and a DLL entrypoint RVA, while still blocking retained DLL views, DllMain, TLS callbacks, and arbitrary PE execution.

Fresh evidence:

- `bin/simple check` on changed DLL file-bytes source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_file_bytes_spec.spl`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_file_bytes_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2697 files, all checks passed.
- Wine DLL file-bytes changed-file stub scan: pass.

## 2026-05-07 DLL File-Probe Update

The DLL file-probe layer now composes search-order candidate paths with a modeled byte-file table, chooses the first candidate with bytes, and validates those bytes through the PE DLL byte gate. It records search-plus-file evidence while still avoiding real host file opens, persistent DLL views, DllMain, TLS callbacks, and arbitrary PE execution.

Fresh evidence:

- `bin/simple check` on changed DLL file-probe source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_file_probe_spec.spl`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_file_probe_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2698 files, all checks passed.
- Wine DLL file-probe changed-file stub scan: pass.

## 2026-05-07 DLL File-Backed View Update

The DLL file-backed view layer now maps validated DLL file-probe bytes into a retained SimpleOS process image view. It records selected path, mapped base, image size, entrypoint RVA, and OS-VMA evidence while still blocking relocations, import binding, TLS callbacks, DllMain, and arbitrary PE execution.

Fresh evidence:

- `bin/simple check` on changed DLL file-view source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_file_view_spec.spl`: 2 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_file_view_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2699 files, all checks passed.
- Wine DLL file-view changed-file stub scan: pass.

## 2026-05-07 DLL View Relocation Update

The DLL view relocation layer now applies bounded DIR64 relocation mutation evidence to retained DLL file-backed views. It validates the file probe, maps the view, opens a modeled VMA write window, patches copied bytes, restores rx, and keeps DllMain/TLS/arbitrary execution blocked.

Fresh evidence:

- `bin/simple check` on changed DLL view-relocation source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_view_relocation_spec.spl`: 2 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2700 files, all checks passed.
- Wine DLL view-relocation changed-file stub scan: pass.

## 2026-05-07 DLL View Import-Binding Update

The DLL view import-binding layer now composes relocated retained DLL views with bounded import descriptor inventory, modeled KERNEL32/USER32/GDI32 module resolution, and IAT byte patching through a modeled VMA write window. It restores rx permissions and keeps real DLL loads, DllMain, TLS callbacks, and arbitrary execution blocked.

Fresh evidence:

- `bin/simple check` on changed DLL view import-binding source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_view_import_binding_spec.spl`: 2 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_import_binding_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2701 files, all checks passed.
- Wine DLL view import-binding changed-file stub scan: pass.

## 2026-05-07 DLL View TLS-Dispatch Update

The DLL view TLS-dispatch layer now composes import-bound retained DLL views with TLS callback-table planning and records loader-lock/TLS-before-DllMain dispatch evidence. It verifies the callback target maps inside the DLL image while still blocking callback instruction execution, DllMain, and arbitrary PE execution.

Fresh evidence:

- `bin/simple check` on changed DLL view TLS-dispatch source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_view_tls_dispatch_spec.spl`: 2 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_tls_dispatch_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2702 files, all checks passed.
- Wine DLL view TLS-dispatch changed-file stub scan: pass.

## 2026-05-07 DLL View DllMain-Handoff Update

The DLL view DllMain-handoff layer now composes import-bound retained DLL views with TLS callback planning, validates a byte-mapped DLL entrypoint, records loader-lock/TLS-before-DllMain/process-attach handoff evidence, and hard-blocks actual DllMain execution.

Fresh evidence:

- `bin/simple check` on changed DLL view DllMain-handoff source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_view_dllmain_handoff_spec.spl`: 2 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2703 files, all checks passed.
- Wine DLL view DllMain-handoff changed-file stub scan: pass.

## 2026-05-07 DLL View Startup Fault/Rollback Update

The DLL view startup-fault layer now composes the non-executing DllMain handoff with modeled VM fault evidence. It accepts `deliver-seh` startup faults, records SEH dispatch plus loader-lock release/rollback evidence, and keeps TLS callbacks, DllMain, and arbitrary PE instruction execution blocked.

Fresh evidence:

- `bin/simple check` on changed DLL view startup-fault source/spec files plus generated matcher specs: all checks passed.
- `bin/simple test test/lib/common/wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2704 files, all checks passed.
- Wine DLL view startup-fault changed-file stub scan: pass.

## 2026-05-07 Process Entrypoint Startup Fault/Rollback Update

The process entrypoint startup-fault layer now composes import-loader VMA transaction handoff evidence with modeled VM fault evidence. It records SEH dispatch, process loader-lock release, import-loader refcount release, and process VMA rx restoration only for `deliver-seh` execute faults at the imported entrypoint; other fault addresses or policies stay blocked.

Fresh evidence:

- `bin/simple check` on changed process entrypoint startup-fault source/spec files plus generated matcher specs: all checks passed.
- `bin/simple test test/lib/common/wine_process_entrypoint_startup_fault_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2705 files, all checks passed.
- Wine process entrypoint startup-fault changed-file stub scan: pass.

## 2026-05-07 SEH Frame-Chain Dispatch Update

The SEH frame-chain planner now requires an active thread-local frame, stack-contained frame address, mapped handler address, and `deliver-seh` fault policy before SEH dispatch handoff evidence is emitted. The process entrypoint startup-fault layer has a `with_seh` path that composes this frame-chain gate before reporting `seh-ready`, while still blocking handler execution and arbitrary PE dispatch.

Fresh evidence:

- `bin/simple check` on changed SEH frame-chain source/spec files plus generated matcher specs: all checks passed.
- `bin/simple test test/lib/common/wine_seh_frame_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple test test/lib/common/wine_process_entrypoint_startup_fault_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_seh_frame_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple check src/lib`: 2706 files, all checks passed.
- SEH frame-chain changed-file `git diff --check` and stub scan: pass.

## 2026-05-07 Executable-Environment MDSOC Gate Update

The SimpleOS executable-environment gate now requires explicit MDSOC+ ownership
markers before VM/full-OS/container/X11 serial-log evidence can become readiness
evidence. The gate requires an owning capsule, public port/facade, and resident
ECS state owner marker in addition to QEMU, full OS boot, kernel service,
process, VM space, filesystem, window system, network, namespace facets, and
NVFS rootfs evidence.

Fresh evidence:

- `bin/simple check` on executable-environment gate source/spec files: all checks passed.
- `bin/simple test test/lib/common/wine_simpleos_exec_env_gate_spec.spl --mode=interpreter --clean`: 7 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_exec_env_mdsoc_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple check` on generated executable-environment matcher specs: all checks passed.
- `bin/simple check src/lib`: 2706 files, all checks passed.
- Executable-environment changed-file `git diff --check` and stub scan: pass.
- Aggregate `simpleos_wine_substrate_spec` now completes under the watchdog after moving REQ-018 dispatch-plan coverage to the focused `simpleos_wine_known_console_dispatch_spec.spl`.

## 2026-05-07 Executable-Environment OS Service Update

The SimpleOS executable-environment gate now keeps `full-os-boot` separate from
concrete kernel service evidence. Wine-facing readiness requires syscall ABI,
scheduler, and VFS service markers before process, VM, filesystem, window,
network, container, and MDSOC+ evidence can make the executable environment
ready.

Fresh evidence:

- `bin/simple check` on executable-environment gate source/spec/system files: all checks passed.
- `bin/simple test test/lib/common/wine_simpleos_exec_env_gate_spec.spl --mode=interpreter --clean`: 8 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_exec_env_mdsoc_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- Generated matcher specs changed with the executable-environment specs and are included in this slice.
- `bin/simple check src/lib`: 2706 files, all checks passed.

Conservative boundary: this is readiness evidence for OS-backed execution
services. It does not create a full container runtime, live VM enforcement path,
or arbitrary Wine/PE execution environment.

## 2026-05-07 PEB/TEB Startup Evidence Update

The NT startup substrate now has a bounded PEB/TEB initialization gate. It
requires SimpleOS process/thread identity, address-space, stack-bounds, process
parameters, TLS vector, and MDSOC process/thread port evidence before
`NtQueryInformationProcess` and `NtQueryInformationThread` can report PEB/TEB
addresses through the modeled NTDLL process-info bridge.

Fresh evidence:

- `bin/simple check` on PEB/TEB and NTDLL process-info source/spec/system files: all checks passed.
- `bin/simple test test/lib/common/wine_peb_teb_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- `bin/simple test test/lib/common/wine_ntdll_process_info_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple check` on generated matcher specs: all checks passed.
- `bin/simple check src/lib`: 2707 files, all checks passed.

Conservative boundary: this validates startup evidence only. It does not execute
arbitrary TLS callbacks, mutate a live PEB/TEB, or run general PE code.

## 2026-05-07 PEB/TEB Loader-Lock Update

The PEB/TEB startup gate now has a loader-lock variant that composes the
bounded KERNEL32 critical-section sequence (`InitializeCriticalSection`,
`EnterCriticalSection`, `LeaveCriticalSection`, `DeleteCriticalSection`) around
PEB/TEB/TLS/process-parameter evidence before reporting startup readiness.

Fresh evidence:

- `bin/simple check src/lib/common/wine_peb_teb.spl test/lib/common/wine_peb_teb_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl` passed.
- `bin/simple test test/lib/common/wine_peb_teb_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: 2 examples, 0 failures.
- `bin/simple check test/lib/common/.spipe_matchers_wine_peb_teb_spec.spl doc/06_spec/app/simpleos/feature/.spipe_matchers_simpleos_wine_peb_teb_spec.spl` passed.
- `bin/simple check src/lib`: 2707 files, all checks passed.

Conservative boundary: this models loader-lock ordering only. It still does not
run live TLS callbacks, execute DllMain, mutate PEB/TEB memory, or transfer
control to arbitrary PE code.

## 2026-05-07 PEB/TEB Memory-Write Gate Update

The PEB/TEB startup layer now has a bounded memory-write gate. It composes the
existing PEB/TEB/TLS/process-parameter startup evidence with SimpleOS VM access
checks and requires writable pages for the PEB, TEB, TLS vector, and process
parameters before reporting modeled mutation readiness.

Fresh evidence:

- `bin/simple check src/lib/common/wine_peb_teb.spl test/lib/common/wine_peb_teb_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl` passed.
- `bin/simple test test/lib/common/wine_peb_teb_spec.spl --mode=interpreter --clean`: 7 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple check` on generated PEB/TEB matcher specs: all checks passed.
- `bin/simple check src/lib`: 2707 files, all checks passed.

Conservative boundary: this records modeled writable-page readiness only. It
does not execute arbitrary TLS callbacks, run DllMain, perform byte-accurate
Windows PEB/TEB layout writes, or transfer control to arbitrary PE code.

## 2026-05-07 PEB/TEB NTDLL Write-Handoff Update

The NTDLL process/thread information bridge now has a write-aware PEB/TEB path.
It requires the modeled PEB/TEB memory-write readiness result before reporting
`NtQueryInformationProcess` and `NtQueryInformationThread` PEB/TEB addresses,
so process-info handoff can no longer rely only on aligned startup addresses.

Fresh evidence:

- `bin/simple check src/lib/common/wine_ntdll_process_info.spl test/lib/common/wine_ntdll_process_info_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl` passed.
- `bin/simple test test/lib/common/wine_ntdll_process_info_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- `bin/simple check` on generated NTDLL process-info and PEB/TEB matcher specs: all checks passed.
- `bin/simple check src/lib`: 2707 files, all checks passed.

Conservative boundary: this composes modeled write readiness with process-info
queries. It still does not perform byte-accurate Windows PEB/TEB writes, run TLS
callbacks, execute DllMain, or transfer control to arbitrary PE code.

## 2026-05-07 DLL View DllMain PEB/TEB Handoff Update

The retained DLL view DllMain handoff now has a PEB/TEB-aware variant. It
requires the bounded PEB/TEB/TLS/process-parameter startup gate plus the modeled
KERNEL32 loader-lock critical-section sequence before reporting DllMain
process-attach handoff readiness.

Fresh evidence:

- `bin/simple check` on changed DllMain handoff, critical-section, unit, and system spec files: all checks passed.
- `bin/simple test test/lib/common/wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: 2 examples, 0 failures.
- `bin/simple test test/lib/common/wine_kernel32_critical_section_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple check` on generated DllMain-handoff matcher specs: all checks passed.
- `bin/simple check src/lib`: 2707 files, all checks passed.

Conservative boundary: this composes startup evidence with a non-executing
DllMain handoff. It still does not run live TLS callbacks, execute DllMain,
mutate PEB/TEB memory, or transfer control to arbitrary PE code.

## 2026-05-07 Wine Aggregate Watchdog Split

REQ-018 known-console dispatch planning now has focused system coverage in
`doc/06_spec/app/simpleos/feature/simpleos_wine_known_console_dispatch_spec.spl`.
The aggregate Wine substrate spec retains the prerequisite and boundary checks
through REQ-017 and no longer repeats the heavy dispatch-plan path that pushed
the aggregate system spec over the Simple test watchdog.

Fresh evidence:

- `bin/simple check` on aggregate and focused REQ-018 system specs: all checks passed.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: 30 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_known_console_dispatch_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- Generated matcher specs checked clean; changed-file `git diff --check` and stub scan: pass.

Conservative boundary: this improves verification shape only. It does not add
new arbitrary PE coverage or broader Wine compatibility.

## 2026-05-07 Executable-Environment Matrix Update

The top-level Wine substrate matrix now exposes the SimpleOS executable-environment gate directly through `wine_substrate_exec_env_gate` and the `exec_env` capability row. This makes VM/full-OS/container evidence a first-class Wine readiness prerequisite instead of an implicit side gate.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test test/lib/common/wine_simpleos_exec_env_gate_spec.spl`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: `exec_env=verified` means the controlled Wine path has explicit SimpleOS VM/full-OS/container evidence. It does not by itself imply a complete Wine port or arbitrary PE compatibility.

## 2026-05-07 WM X11 And Container Evidence Tightening

The Wine-facing WM bridge now keeps X11 production binding blocked until SimpleOS-side cursor and clipboard evidence exist alongside window records and framebuffer presents. The executable-environment gate now requires container namespace facets for pid, fs, ipc, net, and capability isolation separately, plus an NVFS-backed container rootfs marker.

Fresh evidence:

- `bin/simple check src/lib/common/ui/wine_simpleos_window_bridge.spl src/lib/common/ui/wine_x11_adapter.spl src/lib/common/wine_simpleos_exec_env_gate.spl test/lib/common/ui/wine_simpleos_window_bridge_spec.spl test/lib/common/ui/wine_x11_adapter_spec.spl test/lib/common/wine_simpleos_exec_env_gate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/ui/wine_simpleos_window_bridge_spec.spl`: 7 examples, 0 failures.
- `bin/simple test test/lib/common/ui/wine_x11_adapter_spec.spl`: 11 examples, 0 failures.
- `bin/simple test test/lib/common/wine_simpleos_exec_env_gate_spec.spl`: 6 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is sharper X11-class and container/VM executable-environment evidence. It is still not a live full X server, complete container runtime, or arbitrary Wine/PE execution environment.

## 2026-05-07 Data-Backed PE Gate Update

`wine_pe_gate_from_image` now derives PE loader readiness from actual PE bytes before applying policy evidence. The gate requires a valid PE32+ x86_64 console header, bounded sections, a valid import descriptor, relocation runtime evidence, TLS callback handling evidence, structured loader errors, safe mapping, and no-exec-before-gates policy.

Fresh evidence:

- `bin/simple check src/lib/common/wine_pe_gate.spl src/lib/common/wine_substrate.spl test/lib/common/wine_pe_gate_spec.spl test/lib/common/wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_pe_gate_spec.spl`: 9 examples, 0 failures.
- `bin/simple test test/lib/common/pe_coff_header_spec.spl`: 14 examples, 0 failures.
- `bin/simple test test/lib/common/wine_pe_loader_runtime_spec.spl`: 4 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this verifies a bounded PE readiness gate for the controlled Wine path. It is still not an arbitrary PE loader, full relocation engine, full TLS callback dispatcher, or full Wine loader.

## 2026-05-07 Dynamic-Loader Evidence Update

The dynamic-loader adapter now requires bounded NTDLL loader-resolution evidence before full adapter readiness. `wine_dynload_adapter_gate_with_loader_result` composes the existing coexistence API gate with `LdrLoadDll`, `LdrGetProcedureAddress`, and `LdrUnloadDll` results, and keeps failed module/procedure resolution blocked with structured errors.

Fresh evidence:

- `bin/simple check src/lib/common/wine_dynload_adapter.spl src/lib/common/wine_substrate.spl test/lib/common/wine_dynload_adapter_spec.spl test/lib/common/wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_dynload_adapter_spec.spl`: 8 examples, 0 failures.
- `bin/simple test test/lib/common/wine_ntdll_loader_spec.spl`: 3 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded loader-resolution evidence for the Wine substrate. It does not provide a general Unix dynamic loader, arbitrary DLL loading, or full Wine loader behavior.

## 2026-05-07 Thread/Wait Evidence Update

The thread adapter now requires modeled NT wait evidence before full adapter readiness. `wine_thread_adapter_gate_with_wait_result` composes the thread/TLS/wait API gate with a completed `WaitForSingleObject` result and keeps timeout or invalid-handle waits blocked with structured errors.

Fresh evidence:

- `bin/simple check src/lib/common/wine_thread_adapter.spl src/lib/common/wine_substrate.spl test/lib/common/wine_thread_adapter_spec.spl test/lib/common/wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_thread_adapter_spec.spl`: 8 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_thread_wait_spec.spl`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded thread/wait evidence for the Wine substrate. It does not provide real preemptive Windows thread semantics, APCs, fibers, full wait sets, or exception delivery.

## 2026-05-07 POSIX/File-I/O Evidence Update

The POSIX adapter now requires bounded KERNEL32 file-I/O evidence before full adapter readiness. `wine_posix_adapter_gate_with_file_io_result` composes the fd/process/stdio/wait/timer/socket/path/errno adapter gate with `CreateFileW`, `ReadFile`, `GetFileType`, and `CloseHandle` results, and keeps failed file-open/read paths blocked with structured errors.

Fresh evidence:

- `bin/simple check src/lib/common/wine_posix_adapter.spl src/lib/common/wine_substrate.spl test/lib/common/wine_posix_adapter_spec.spl test/lib/common/wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_posix_adapter_spec.spl`: 9 examples, 0 failures.
- `bin/simple test test/lib/common/wine_kernel32_file_io_spec.spl`: 3 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded file-I/O evidence for the Wine substrate. It does not provide complete POSIX semantics, sockets, poll/select, locking/sharing, async cancellation, or arbitrary filesystem behavior.

## 2026-05-07 Service-Control Evidence Update

The service adapter now requires bounded ADVAPI32 service-control evidence before full adapter readiness. `wine_service_adapter_gate_with_service_result` composes the existing IPC, handle, audio, font, crypto, HID, printing, multimedia, and host-feature gate with an ordered service manager open/create/open/start/close result, and keeps failed service-control paths blocked with structured errors.

Fresh evidence:

- `bin/simple check src/lib/common/wine_service_adapter.spl src/lib/common/wine_substrate.spl test/lib/common/wine_service_adapter_spec.spl test/lib/common/wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_service_adapter_spec.spl`: 8 examples, 0 failures.
- `bin/simple test test/lib/common/wine_advapi32_service_spec.spl`: 2 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded service-control evidence for the Wine substrate. It does not provide a real Windows service control manager, service process lifetime, service accounts, dependency ordering, recovery actions, or arbitrary service-host behavior.

## 2026-05-07 Peripheral Evidence Update

The substrate matrix no longer marks `audio`, `fonts`, or `input` verified from the broad `host=verified` gate. Those rows now require explicit `audio=verified`, `fonts=verified`, and `input=verified` evidence. The service adapter exposes bounded peripheral gates for waveOut buffer submission, font discovery/glyph raster evidence, and keyboard/pointer/message dispatch evidence.

Fresh evidence:

- `bin/simple check src/lib/common/wine_service_adapter.spl src/lib/common/wine_substrate.spl test/lib/common/wine_service_adapter_spec.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_service_adapter_spec.spl`: 11 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded peripheral evidence for the substrate matrix. It does not provide real DirectSound/MME devices, complete fontconfig/GDI font rendering, raw input, XInput, joystick support, or arbitrary multimedia behavior.

## 2026-05-07 Registry Matrix Update

The top-level Wine substrate matrix now exposes registry readiness through a first-class `registry` capability row. The row points at bounded ADVAPI32 registry roundtrip evidence and NTDLL registry query evidence instead of leaving registry behavior hidden in lower-level bridge tests.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_advapi32_registry_spec.spl`: 2 examples, 0 failures.
- `bin/simple test test/lib/common/wine_ntdll_registry_spec.spl`: 3 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded registry bridge evidence for startup probes. It does not provide a persistent Windows registry hive, ACL/security semantics, reflection, transactions, notifications, or full registry virtualization.

## 2026-05-07 USER32/GDI32 Matrix Update

The top-level Wine substrate matrix now exposes `user32` and `gdi32` capability rows. `user32` points at the bounded SimpleOS-backed `CreateWindowExW`/`ShowWindow`/`UpdateWindow`/`DefWindowProcW` lifecycle and message-loop bridge tests. `gdi32` points at the bounded `CreateCompatibleDC`/`TextOutW`/`BitBlt`/`DeleteDC` text blit bridge tests.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_user32_window_spec.spl`: 4 examples, 0 failures.
- `bin/simple test test/lib/common/wine_gdi32_drawing_spec.spl`: 2 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: this is bounded USER32/GDI32 bridge evidence for controlled GUI probes. It does not provide a full USER32 window manager, complete message pump, menus/dialogs/controls, GDI object lifetime, region/clipping semantics, printer DCs, or arbitrary GUI application compatibility.

## 2026-05-07 Full Wine Gate Boundary

The substrate now has a separate `wine_substrate_full_wine_gate` in addition to `wine_substrate_hello_exe_gate`. The full gate requires every tracked Wine substrate row: process, executable environment, VM, renderer, USER32, GDI32, KERNEL32 core, host, POSIX, registry, pthread, dynamic loading, audio, fonts, input, PE loader, async, and NT bridge. This keeps the controlled hello milestone from being used as proof of full Wine readiness.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 18 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 16 examples, 0 failures.

Conservative boundary: this is a readiness classifier, not the missing implementations themselves. It makes incomplete full-Wine readiness explicit until every tracked row has concrete evidence.

## 2026-05-07 KERNEL32 Core Matrix Update

The top-level Wine substrate matrix now exposes `kernel32_core` as a first-class capability row. Its evidence command covers bounded KERNEL32 virtual memory, heap, TLS/FLS, synchronization event, error state, atom table, time/version, startup info, interlocked, and process-environment bridge specs.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test` on the KERNEL32 core specs listed by the row: virtual memory 2/0, heap 3/0, TLS 4/0, FLS 4/0, sync event 3/0, error state 4/0, atom table 4/0, time/version 3/0, startup info 3/0, interlocked 4/0, process environment 5/0.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 18 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 16 examples, 0 failures.

Conservative boundary: this is bounded KERNEL32 core API evidence. It does not provide every KERNEL32 export, true Windows object lifetime, complete virtual memory semantics, loader integration, or arbitrary process execution.

## 2026-05-07 KERNEL32 Process Environment Fix

`src/lib/common/wine_kernel32_process_env.spl` now uses module-unique helper
names for its bounded symbol-family and sequence gates. This prevents the
process-environment bridge from resolving a sibling `_sequence_gate` helper and
incorrectly reporting `GetCommandLineW` as a virtual-memory wrong-category
symbol.

Fresh evidence:

- `bin/simple check src/lib/common/wine_kernel32_process_env.spl test/lib/common/wine_kernel32_process_env_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_kernel32_process_env_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_process_env_spec.spl --mode=interpreter --clean`: 9 examples, 0 failures.

Conservative boundary: this makes the bounded KERNEL32 process-environment
bridge dispatchable for the modeled startup calls. It does not implement the
full Windows process environment, environment block ownership rules, inherited
process parameters, locale/codepage behavior, or arbitrary process creation.

## 2026-05-07 MDSOC+ Architecture Alignment

The Wine/SimpleOS architecture docs now explicitly base the substrate on the
repo MDSOC+ contract: common Wine adapters are shared tree-node facades under
`src/lib/common/`, kernel and drivers remain MDSOC-only, and resident userland
WM/process/container/Wine service state must use an MDSOC outer capsule with an
ECS inner world.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 18 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 16 examples, 0 failures.

Conservative boundary: this is an architecture constraint and documentation
alignment. It does not make full Wine, a complete X server, kernel page-table
enforcement, or arbitrary containerized PE execution complete.

## 2026-05-07 Proton Readiness Boundary

The repo now has a first-class Proton readiness gate above the Wine substrate.
`src/lib/common/wine_proton_gate.spl` requires full Wine readiness first, then
Steam runtime, pressure-vessel style container, Proton launcher, Vulkan, DXVK,
VKD3D-Proton, Steamworks bridge, controller input, shader cache, and
esync-or-fsync evidence.

Fresh evidence:

- `bin/simple check src/lib/common/wine_proton_gate.spl test/lib/common/wine_proton_gate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_proton_gate_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.

Conservative boundary: this is a Proton readiness classifier, not Proton
itself. It does not implement upstream Proton, Steam client integration, a
Linux ABI, Vulkan driver support, DXVK, VKD3D-Proton, or arbitrary Windows game
compatibility.

## 2026-05-07 KERNEL32 File And Loader Evidence Expansion

The `kernel32_core` substrate evidence row now includes all currently passing
bounded KERNEL32 bridge specs, including file I/O, file metadata,
file-management, thread wait, critical section, local/global memory, module
loader, path, and process identity coverage.

Fresh evidence:

- `bin/simple check src/lib/common/wine_kernel32_file_management.spl src/lib/common/wine_kernel32_file_metadata.spl test/lib/common/wine_kernel32_file_management_spec.spl test/lib/common/wine_kernel32_file_metadata_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_kernel32_file_management_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/wine_kernel32_file_metadata_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- Individual `bin/simple test` runs for every `test/lib/common/wine_kernel32_*_spec.spl`: all passing after the file-management and file-metadata helper fixes.
- `bin/simple test test/lib/common/wine_substrate_spec.spl --mode=interpreter --clean`: 18 examples, 0 failures.

Conservative boundary: this expands tracked bounded KERNEL32 startup evidence.
It does not provide the full KERNEL32 export set, complete object lifetime,
true Windows file sharing semantics, complete loader behavior, or arbitrary PE
execution.

## 2026-05-07 GUI Milestone Production Evidence Fix

The controlled GUI hello milestone now carries SimpleOS-side cursor and
clipboard evidence into the `/win` bridge before binding Wine-facing X11 state
to SimpleOS production evidence. This closes the remaining `wine_gui_hello_spec`
failure without relaxing the X11 production gate.

Fresh evidence:

- `bin/simple check src/lib/common/wine_gui_hello.spl test/lib/common/wine_gui_hello_spec.spl src/app/wine_gui_hello/main.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_gui_hello_spec.spl --mode=interpreter --clean`: 2 examples, 0 failures.
- `bin/simple run src/app/wine_gui_hello/main.spl`: emitted `window=SimpleOS Wine GUI Hello`, `text=Hello from SimpleOS Wine`, and checksum evidence.
- `bin/simple test test/integration/app/wine_gui_hello_command_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- Individual `bin/simple test` runs for every `test/lib/common/wine_*_spec.spl`: 0 failing Wine specs.

Conservative boundary: this completes the controlled GUI milestone evidence
path only. It is not a full X11 server, complete USER32 message pump, Wine
graphics driver, compositor integration, or arbitrary GUI application support.

## 2026-05-07 Structured Proton Runtime Evidence

The Proton gate now has a structured runtime-evidence layer in addition to the
flat readiness classifier. `wine_proton_runtime_gate` requires Steam runtime
x86_64 ABI evidence, a pressure-vessel-style container rootfs with pid/fs/ipc/
net/capability facets, Vulkan loader/device evidence, DXVK, VKD3D-Proton,
shader cache, Proton launcher, Steamworks bridge, controller input, and
esync-or-fsync evidence before deriving the legacy Proton feature string.

Fresh evidence:

- `bin/simple check src/lib/common/wine_proton_runtime.spl test/lib/common/wine_proton_runtime_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_proton_runtime_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_proton_gate_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl --mode=interpreter --clean`: includes structured runtime evidence coverage.

Conservative boundary: this is still a Proton readiness contract and modeled
runtime evidence path. It does not implement upstream Proton, Steam client
login, pressure-vessel execution, Linux ABI syscall coverage, Vulkan drivers,
DXVK/VKD3D shader execution, or arbitrary Windows game compatibility.

## 2026-05-07 Non-Wine Proton Subsystem Completion

The Proton prerequisites outside Wine itself now have their own common facade:
`src/lib/common/proton_runtime_subsystems.spl`. It independently gates Steam
runtime ABI, pressure-vessel container/rootfs/namespaces, Vulkan loader/device,
DXVK, VKD3D-Proton, shader cache, Proton launcher, Steamworks bridge,
controller input, and esync-or-fsync evidence. `wine_proton_runtime_gate` now
composes this non-Wine facade and adds only the outer full-Wine dependency.

Fresh evidence:

- `bin/simple check src/lib/common/proton_runtime_subsystems.spl src/lib/common/wine_proton_runtime.spl test/lib/common/proton_runtime_subsystems_spec.spl test/lib/common/wine_proton_runtime_spec.spl doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/proton_runtime_subsystems_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_proton_runtime_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl --mode=interpreter --clean`: includes non-Wine subsystem evidence coverage.

Conservative boundary: this completes the modeled non-Wine Proton prerequisite
gates only. It intentionally excludes full Wine itself and does not implement
actual Steam runtime process execution, pressure-vessel process launch, Vulkan
driver execution, DXVK/VKD3D shader translation, or game compatibility.

## 2026-05-07 Non-Wine Proton Session Planning

`src/lib/common/proton_session.spl` now models the next non-Wine Proton layer:
session requests and planned launch records. It validates Steam app id, compat
prefix, executable path, and non-Wine subsystem evidence before producing a
planned launch command and runtime feature evidence.

Fresh evidence:

- `bin/simple check src/lib/common/proton_session.spl test/lib/common/proton_session_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/proton_session_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl --mode=interpreter --clean`: includes non-Wine launch-session planning coverage.

Conservative boundary: this is a launch-session plan, not execution. It does
not start Steam, Wine, Proton, pressure-vessel, Vulkan, or any game process.

## 2026-05-07 Proton Session Plan Command

`src/app/proton_session_plan/main.spl` now exposes the non-Wine Proton session
planner as a command. It prints the Steam app id, compat prefix, planned
executable command, status, and runtime feature evidence for the fixture
non-Wine Proton runtime.

Fresh evidence:

- `bin/simple check src/app/proton_session_plan/main.spl test/integration/app/proton_session_plan_command_spec.spl`: all checks passed.
- `bin/simple run src/app/proton_session_plan/main.spl`: emitted `app_id=480`, `prefix=steamapps/compatdata/480/pfx`, `command=hl2.exe -novid`, `status=planned`, and Proton runtime feature evidence.
- `bin/simple test test/integration/app/proton_session_plan_command_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.

Conservative boundary: this command reports a planned session only. It does
not execute Steam, Wine, Proton, pressure-vessel, Vulkan, or game code.

## 2026-05-07 Proton Dry-Run Launch Handoff

The non-Wine Proton session planner now emits a bounded launch handoff record.
`proton_session_launch_handoff(plan, true)` returns `dry-run-ready` with app id,
compat prefix, launch command, pressure-vessel container profile, and runtime
feature evidence. Calling it with `dry_run == false` remains blocked with
`execution-not-implemented`.

Fresh evidence:

- `bin/simple check src/lib/common/proton_session.spl test/lib/common/proton_session_spec.spl src/app/proton_session_plan/main.spl test/integration/app/proton_session_plan_command_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/proton_session_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- `bin/simple run src/app/proton_session_plan/main.spl`: emitted `status=dry-run-ready`, a pressure-vessel container profile, and runtime feature evidence.

Conservative boundary: this is still non-executing handoff evidence. Real
Steam/Proton/pressure-vessel/Wine/game process execution remains blocked.

## 2026-05-07 Proton Executable-Environment Composition

`proton_session_launch_handoff_with_exec_env(...)` now composes non-Wine Proton
runtime evidence with the SimpleOS MDSOC executable-environment gate before any
dry-run Proton handoff is reported. Missing VM/full-OS/container/MDSOC evidence
returns `exec-env:<missing-state>` and keeps the handoff blocked.

Fresh evidence:

- `bin/simple check` on Proton session/app/system spec files: all checks passed.
- `bin/simple test test/lib/common/proton_session_spec.spl --mode=interpreter --clean`: includes MDSOC executable-environment rejection and ready handoff coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_proton_substrate_spec.spl --mode=interpreter --clean`: includes Proton executable-environment composition coverage.
- `bin/simple test test/integration/app/proton_session_plan_command_spec.spl --mode=interpreter --clean`: command prints `exec_env=mdsoc-ready`.
- `bin/simple run src/app/proton_session_plan/main.spl`: emitted `exec_env=mdsoc-ready`.
- `bin/simple check` on generated Proton matcher specs: all checks passed.
- `bin/simple check src/lib`: 2706 files, all checks passed.
- Proton executable-environment changed-file `git diff --check` and stub scan: pass.

Conservative boundary: this still performs no Steam, Proton, pressure-vessel,
Wine, Vulkan, DXVK/VKD3D, or game process execution.

## 2026-05-07 Wine Process Session Handoff

`src/lib/common/wine_process_session.spl` now exposes a Wine-side process
session boundary. It validates executable path and working directory, allows a
planned session for the controlled `hello.exe` milestone when the hello gate is
ready, requires the full Wine gate for arbitrary `.exe` sessions, and emits
only dry-run launch handoff records until real process execution exists.

Fresh evidence:

- `bin/simple check src/lib/common/wine_process_session.spl test/lib/common/wine_process_session_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: 4 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes Wine process-session handoff coverage.

Conservative boundary: this adds a process-session/handoff artifact, not a
general Wine executor. Arbitrary `.exe` execution remains blocked until full
Wine readiness and an actual process execution boundary are implemented.

## 2026-05-07 Wine Process Session Plan Command

`src/app/wine_process_session_plan/main.spl` now exposes the controlled Wine
process-session handoff as a command. It reports the command, substrate
readiness, and dry-run status for the controlled `hello.exe` path.

Fresh evidence:

- `bin/simple check src/app/wine_process_session_plan/main.spl test/integration/app/wine_process_session_plan_command_spec.spl`: all checks passed.
- `bin/simple run src/app/wine_process_session_plan/main.spl`: emitted `command=hello.exe`, `readiness=controlled-hello-ready`, and `status=dry-run-ready`.
- `bin/simple test test/integration/app/wine_process_session_plan_command_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.

Conservative boundary: this command reports dry-run handoff evidence only. It
does not execute Wine or arbitrary Windows programs.

## 2026-05-07 Controlled Wine Process Session Execution

`src/lib/common/wine_process_session.spl` now routes the planned controlled
`hello.exe` session through the existing VM-backed hello executor. The process
session result reports `execution=executed`, preserves the process command, and
returns `Hello from SimpleOS Wine` with exit code 0.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes controlled session execution and arbitrary-session rejection coverage.
- `bin/simple run src/app/wine_process_session_plan/main.spl`: emits `command=hello.exe`, `readiness=controlled-hello-ready`, `handoff=dry-run-ready`, `execution=executed`, and hello stdout.
- `bin/simple test test/integration/app/wine_process_session_plan_command_spec.spl --mode=interpreter --clean`: covers the command output.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-012 controlled session execution coverage.

Conservative boundary: this is controlled `hello.exe` execution only. Arbitrary
PE/DLL loading, full Win32/NT behavior, generic Wine process execution, and
Steam/Proton game execution remain blocked.

## 2026-05-07 Arbitrary Process Image Validation Boundary

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_validate_full_image(...)` for full-Wine process plans. It requires
a planned full-Wine session, then runs the PE header, section, directory,
import, relocation, TLS, and image-map gates before reporting
`image-validated`.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes full-image validation, malformed-image rejection, and controlled-plan rejection coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-013 process image validation coverage.

Conservative boundary: this validates arbitrary process images only. It does
not load arbitrary DLLs, bind imports beyond existing gate checks, or execute
arbitrary PE code.

## 2026-05-07 Arbitrary Process Import Inspection Boundary

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_inspect_full_imports(...)` for image-validated full-Wine process
plans. It inspects the first import descriptor with a caller-provided symbol
limit and returns the DLL name plus imported symbols.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes first-import inspection and invalid symbol-limit coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-014 import inspection coverage.
- `bin/simple test test/lib/common/pe_coff_header_spec.spl --mode=interpreter --clean`: keeps the underlying import parser covered.

Conservative boundary: this is import inspection only. It does not perform
arbitrary DLL loading, import binding, thunk patching, or arbitrary PE
execution.

## 2026-05-07 Bounded Process Import Binding Plan

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_bind_known_kernel32_imports(...)` for image-validated full-Wine
process plans. It reuses the bounded first-import inspection result, extracts
symbol binding RVAs, and returns the supported KERNEL32 console binding
sequence when the import table matches the existing NT import resolver plan.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes KERNEL32 binding-plan and rejected incomplete-binding coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-015 process import binding-plan coverage.
- `bin/simple test test/lib/common/wine_nt_import_spec.spl --mode=interpreter --clean`: keeps the underlying NT import binding planner covered.

Conservative boundary: this is a binding plan only. It does not load arbitrary
DLLs, patch import thunks, dispatch imported functions for arbitrary code, or
execute arbitrary PE images.

## 2026-05-07 Guarded Import Thunk Patch Plan

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_plan_import_thunk_patches(...)` for full-Wine process plans with
supported KERNEL32 bindings. It emits the explicit import-thunk evidence needed
by the CPU execution gate: table validity, symbol resolution, binding match,
and guarded IAT status.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes guarded thunk-patch planning and rejected binding coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-016 guarded import-thunk patch plan coverage.
- `bin/simple test test/lib/common/wine_cpu_exec_spec.spl --mode=interpreter --clean`: keeps the downstream CPU gate requirements covered.

Conservative boundary: this is still a patch plan. It does not mutate import
tables, map process memory writable, dispatch imported functions, or execute
arbitrary PE images.

## 2026-05-07 Process CPU Dispatch Preflight

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_cpu_dispatch_preflight(...)`. It composes the guarded
import-thunk evidence produced by the process loader path with caller-provided
CPU execution evidence, then runs both `wine_cpu_execution_gate(...)` and
`wine_instruction_dispatch_gate(...)`.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes CPU preflight acceptance and missing-evidence rejection coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-017 CPU dispatch preflight coverage.
- `bin/simple test test/lib/common/wine_cpu_exec_spec.spl --mode=interpreter --clean`: keeps CPU and instruction dispatch gates covered.

Conservative boundary: this is a preflight gate only. It does not dispatch
instructions, call imported functions, or execute arbitrary PE images.

## 2026-05-07 Bounded Known-Console Dispatch Plan

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_plan_known_console_dispatch(...)`. It requires the process CPU
preflight to pass, then decodes the known console instruction sequence and
returns the planned imported-call sequence and counts.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_spec.spl --mode=interpreter --clean`: includes known-console dispatch planning and CPU-preflight rejection coverage.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: includes REQ-018 known-console dispatch plan coverage.
- `bin/simple test test/lib/common/wine_hello_dispatch_spec.spl --mode=interpreter --clean`: keeps the downstream known-dispatch path covered.

Conservative boundary: this is a decoded dispatch plan only. It does not step
instructions, call imported functions, or execute arbitrary PE images.

## 2026-05-07 Bounded Known-Console Process Execution

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_execute_known_console(...)`. It requires the full-Wine
process-session gates, image validation, import inspection, KERNEL32 binding,
guarded thunk evidence, CPU dispatch preflight, and bounded known-console
dispatch plan before running the existing modeled NT bridge path.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_known_console_spec.spl --mode=interpreter --clean`: covers successful known-console process execution and missing-CPU-evidence rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl --mode=interpreter --clean`: includes REQ-019 known-console process execution coverage.
- `bin/simple test test/lib/common/wine_hello_dispatch_spec.spl --mode=interpreter --clean`: keeps the modeled NT bridge dispatch path covered.

Conservative boundary: this executes only the decoded known-console sequence.
It is not arbitrary PE execution, arbitrary DLL loading, general x86_64
instruction stepping, or game compatibility.

## 2026-05-07 Bounded Process Module Resolution

`src/lib/common/wine_process_session.spl` now exposes
`wine_process_resolve_known_kernel32_module(...)` and
`wine_process_resolve_known_kernel32_module_ex(...)`. They require a full-Wine
process-session plan, then route the request through the existing KERNEL32
module-loader bridge to return module handle, procedure address, ordered loader
operations, and rejected/blocked status evidence. The `LoadLibraryExW` process
path accepts the modeled zero-flags case and rejects unsupported flags.
`wine_process_resolve_first_import_module(...)` composes PE import inspection
with the same resolver, allowing a validated full-Wine process image to resolve
a requested procedure against its first imported KERNEL32 module through the
curated zero-flags `LoadLibraryExW` loader table.
`wine_process_load_and_bind_known_kernel32_imports(...)` requires that
module-resolution evidence before accepting the known KERNEL32 import binding
plan and returns the loader operations, module handle, call sequence, and
binding count as one process-session result. It now reuses one bounded import
inspection for module resolution and binding rather than inspecting the same
first import table twice.
`wine_process_plan_import_thunk_patches(...)` now consumes the explicit bounded
record plan, so thunk patch evidence carries module-loader and patch-record
preconditions before CPU dispatch preflight can pass.
`wine_process_cpu_dispatch_preflight(...)` now rejects missing non-import CPU
evidence before running the heavier import-record planning path, preserving the
same blocked status while avoiding aggregate-spec watchdog timeouts.
`wine_import_thunk_binding_gate(...)` now requires those module-loader evidence
tokens too, preventing direct CPU preflight callers from reusing the older
thunk-only evidence envelope.
`wine_process_plan_known_kernel32_thunk_patch_records(...)` expands the
loaded-and-bound known KERNEL32 imports into concrete bounded records for the
three modeled thunk slots, including symbol names, thunk indexes, thunk RVAs,
and name RVAs.
Those record RVAs are now derived from `pe_first_import_thunk_bindings(...)`
over the PE first-import lookup thunk table rather than hard-coded in the
process-session planner.
`wine_process_apply_known_kernel32_thunk_patches(...)` now consumes those
records and writes modeled KERNEL32 procedure addresses into a copied PE image
for the same three known thunk slots. This remains bounded fixture image
mutation; writable OS VMA mutation, multi-DLL import-table patching, rollback,
and arbitrary process execution are still outside the completed surface.
`wine_process_prepare_known_console_image(...)` now makes that patched image the
handoff into known-console dispatch and execution, so the bounded decoder and
modeled NT bridge no longer run from the unpatched fixture bytes.
The controlled hello CPU skeleton now uses RIP-relative indirect calls through
the patched KERNEL32 thunk RVAs (`0x2060`, `0x2068`, and `0x2070`) instead of
direct calls to import-name RVAs. This keeps known-console dispatch tied to the
bounded IAT patch records while preserving the arbitrary-instruction block.
`wine_process_map_known_console_image(...)` now maps that patched image through
the modeled SimpleOS process VM adapter before CPU dispatch preflight reports
ready. The evidence records process image mapping, OS process/address-space
identity, OS VMA backing, executable image-map state, and no-host-code-jump
policy at the mapped PE entrypoint.
`wine_process_apply_known_kernel32_thunk_patches_in_vma(...)` now performs the
known thunk writes inside that modeled process image: it opens a bounded VMA
write window, writes the three planned KERNEL32 thunk records, restores `rx`,
and rechecks no-host-code-jump before the mapped-image preflight can pass.
`wine_process_prepare_full_image_handoff(...)` now provides a separate
full-Wine-process handoff: it validates the PE image, maps image plus
stack/guard regions into an OS-backed SimpleOS VM process, verifies the VM
production gate, and reports the mapped entrypoint without executing arbitrary
instructions.
`pe_import_descriptor_table_gate(...)` and
`pe_import_descriptor_summaries(...)` now add a bounded PE import-descriptor
table layer for full-Wine images. `wine_process_validate_full_image(...)` uses
that table-aware gate, while legacy first-import helpers remain strict for the
known-console KERNEL32 binding path. `wine_process_inspect_import_descriptor_table(...)`
exposes the MDSOC process-session view: bounded descriptor count, DLL names,
total thunk-symbol count, and evidence that no DLL binding, thunk patching, or
arbitrary instruction dispatch has occurred. This completes REQ-029 as
inspection/preflight only; multi-DLL loading, import binding, and arbitrary PE
execution remain outside the completed surface.
`pe_import_descriptor_thunk_bindings(...)` now expands those descriptors into
descriptor-qualified thunk records carrying DLL name, descriptor index, symbol,
thunk index, thunk RVA, and import-name RVA. `wine_process_inventory_import_descriptor_thunks(...)`
exposes the process-session inventory as read-only preflight evidence, preserving
the MDSOC boundary between PE table parsing, process-session planning, and any
future loader/binder layer. This completes REQ-030 as data-backed inventory
only; it still performs no module resolution, DLL loading, IAT patching, or
arbitrary execution.
`wine_process_plan_import_dependencies(...)` now turns the descriptor DLL list
into a bounded dependency preflight. It accepts the currently modeled substrate
DLL families (`KERNEL32`, `USER32`, and `GDI32`), deduplicates module names, and
rejects unsupported modules such as `ADVAPI32.dll` before any loader,
resolver, binder, thunk patcher, or instruction-dispatch path runs. This
completes REQ-031 as dependency classification only; it still produces no
module handles, export addresses, or executable state.
`wine_process_plan_import_resolution(...)` now composes dependency planning,
descriptor-qualified thunk inventory, and a modeled module/export table for the
currently covered DLL families. It validates modeled module handles and
procedure addresses for every imported thunk and rejects missing exports such as
`USER32!DialogBoxW` before any IAT patching. This completes REQ-032 as modeled
resolution evidence only; it still performs no real DLL loading, no IAT writes,
and no arbitrary PE execution.
`wine_process_plan_import_descriptor_thunk_patch_records(...)` now converts the
modeled resolution result into multi-DLL thunk patch records that include DLL
name, symbol, descriptor index, lookup thunk RVA, IAT RVA, import-name RVA, and
modeled procedure address. The specs are split between descriptor-table, import
resolution, and patch-record files to keep each full-image validation run below
the Simple test watchdog. This completes REQ-033 as record planning only; it
still performs no VMA permission transition, no IAT write, and no arbitrary PE
execution.
`wine_process_apply_import_descriptor_thunk_patches_in_vma(...)` now consumes
those descriptor-qualified records through the modeled process VMA path. It maps
the validated image shape, opens a bounded write window, writes the modeled
procedure addresses for covered `KERNEL32`/`USER32`/`GDI32` imports into
descriptor `FirstThunk` IAT slots rather than lookup thunk metadata, restores
`rx`, and rechecks no-host-code-jump before reporting success. This completes
REQ-034 as modeled multi-DLL thunk application only; it still performs no real
DLL loading, relocation, TLS initialization, or arbitrary PE execution.
`wine_process_plan_full_image_loader_runtime(...)` now composes the full-image
VM handoff with relocation and TLS callback runtime preflight evidence before
any arbitrary process execution boundary. This completes REQ-035 as loader
runtime preflight only; it still performs no VM relocation mutation, no TLS
callback dispatch, no real DLL loading, and no arbitrary PE execution.
`wine_process_apply_loader_relocations_in_vma(...)` now applies the bounded
DIR64 relocation target through a modeled process VMA write window, restores
`rx`, and preserves no-host-code-jump evidence. This completes REQ-036 as
loader-owned relocation mutation for the copied process image only; it still
performs no TLS callback dispatch, no real DLL loading, no import-table-wide
execution handoff, and no arbitrary PE execution.
`wine_process_record_tls_callback_dispatch(...)` now composes the relocated
process image with TLS callback-table evidence, verifies the first callback RVA
is mapped inside the process image, and records loader-owned dispatch evidence.
This completes REQ-037 as TLS callback dispatch recording only; it still does
not execute callback instructions, load real DLLs, or allow arbitrary PE
execution.
`wine_process_plan_import_loader_state(...)` now owns modeled import-loader
lifetime state for supported multi-DLL imports. It loads the bounded modeled
module table, records refcount growth, releases every loaded handle on success,
and rolls loaded handles back when procedure resolution fails. This completes
REQ-038 as modeled loader state accounting only; it still does not load host
DLLs, execute DLL entrypoints, run TLS callback instructions, patch the IAT, or
allow arbitrary PE execution.
`wine_process_apply_import_loader_transaction_in_vma(...)` now composes modeled
loader state with descriptor-qualified process VMA import patching. It records
module load/release/rollback counts next to patch counts, requires restored
loader refcount evidence before the VMA patch path completes, and aborts before
VMA patching when loader-state resolution rolls back. This completes REQ-039 as
a modeled loader-state-gated import patch transaction only; it still does not
load host DLLs, execute DLL entrypoints, run TLS callback instructions, or allow
arbitrary PE execution.
`wine_process_prepare_imported_entrypoint_handoff(...)` now consumes the import
loader VMA transaction and reports a patched-image entrypoint handoff with
mapped entrypoint evidence. This completes REQ-040 as non-executing entrypoint
handoff only; it still does not execute the PE entrypoint, dispatch arbitrary
instructions, load host DLLs, execute DLL entrypoints, or run TLS callback
instructions.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_module_loader_spec.spl --mode=interpreter --clean`: covers successful KERNEL32 procedure resolution through `LoadLibraryW` and `LoadLibraryExW`, unsupported module rejection, unsupported flag rejection, and controlled-session blocking.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl --mode=interpreter --clean`: includes REQ-020 process module-resolution coverage for both loader calls and rejection paths.
- `bin/simple test test/lib/common/wine_process_session_first_import_module_spec.spl --mode=interpreter --clean`: covers first-import-module resolution and import-inspection gating.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.spl --mode=interpreter --clean`: includes REQ-021 first-import module-loader bridge coverage.
- `bin/simple test test/lib/common/wine_process_session_load_bind_spec.spl --mode=interpreter --clean`: covers load-before-bind composition and module-resolution rejection propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_load_bind_spec.spl --mode=interpreter --clean`: includes REQ-022 load-then-bind coverage.
- `bin/simple test test/lib/common/wine_process_session_thunk_load_bind_spec.spl --mode=interpreter --clean`: covers thunk planning over loaded-and-bound import evidence.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl --mode=interpreter --clean`: includes REQ-023 thunk planning with module-loaded binding coverage.
- `bin/simple test test/lib/common/wine_cpu_exec_spec.spl --mode=interpreter --clean`: covers the tightened CPU import-thunk gate requiring module-loader evidence.
- `bin/simple test test/lib/common/wine_process_session_thunk_records_spec.spl --mode=interpreter --clean`: covers bounded known KERNEL32 thunk patch record planning.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_thunk_records_spec.spl --mode=interpreter --clean`: includes REQ-024 thunk patch record coverage.
- `bin/simple test test/lib/common/pe_coff_header_spec.spl --mode=interpreter --clean`: covers extraction of import lookup thunk RVAs separately from import symbol name RVAs.
- `bin/simple test test/lib/common/wine_process_session_thunk_apply_spec.spl --mode=interpreter --clean`: covers bounded copied-image byte patching for the known KERNEL32 thunk slots.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_thunk_apply_spec.spl --mode=interpreter --clean`: includes REQ-025 bounded import thunk byte patching coverage.
- `bin/simple test test/lib/common/wine_kernel32_module_loader_spec.spl --mode=interpreter --clean`: keeps the lower KERNEL32 module-loader bridge covered.
- `bin/simple test test/lib/common/pe_coff_header_spec.spl --mode=interpreter --clean`: covers bounded multi-descriptor import table validation and descriptor summaries.
- `bin/simple test test/lib/common/wine_process_session_import_descriptor_table_spec.spl --mode=interpreter --clean`: covers full-Wine process-session import descriptor table inspection and descriptor-limit rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl --mode=interpreter --clean`: includes REQ-029 bounded multi-DLL import descriptor inspection coverage.
- `bin/simple test test/lib/common/pe_coff_header_spec.spl --mode=interpreter --clean`: covers descriptor-qualified import thunk binding extraction.
- `bin/simple test test/lib/common/wine_process_session_import_descriptor_table_spec.spl --mode=interpreter --clean`: covers REQ-030 process-session thunk inventory without DLL loading.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl --mode=interpreter --clean`: includes REQ-030 system coverage for descriptor-qualified thunk inventory.
- `bin/simple test test/lib/common/wine_process_session_import_descriptor_table_spec.spl --mode=interpreter --clean`: covers REQ-031 supported dependency planning and unsupported dependency rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl --mode=interpreter --clean`: includes REQ-031 system coverage for import dependency preflight without DLL loading.
- `bin/simple test test/lib/common/wine_process_session_import_resolution_spec.spl --mode=interpreter --clean`: covers REQ-032 modeled import resolution and missing-export rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_resolution_spec.spl --mode=interpreter --clean`: includes REQ-032 system coverage for modeled module/procedure resolution without IAT patching.
- `bin/simple test test/lib/common/wine_process_session_import_patch_records_spec.spl --mode=interpreter --clean`: covers REQ-033 descriptor-qualified thunk patch record planning and missing-export rejection without IAT writes.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_patch_records_spec.spl --mode=interpreter --clean`: includes REQ-033 system coverage for multi-DLL patch record planning.
- `bin/simple test test/lib/common/wine_process_session_import_vma_patch_spec.spl --mode=interpreter --clean`: covers REQ-034 modeled multi-DLL VMA thunk patching and missing-export rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_vma_patch_spec.spl --mode=interpreter --clean`: includes REQ-034 system coverage for the bounded process VMA write window.
- `bin/simple test test/lib/common/wine_process_session_loader_runtime_spec.spl --mode=interpreter --clean`: covers REQ-035 full-image loader runtime preflight and TLS support rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl --mode=interpreter --clean`: includes REQ-035 system coverage for composed image handoff, relocation, and TLS runtime evidence.
- `bin/simple test test/lib/common/wine_process_session_vma_relocation_spec.spl --mode=interpreter --clean`: covers REQ-036 bounded DIR64 relocation mutation through a process VMA write window.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl --mode=interpreter --clean`: includes REQ-036 system coverage for loader-owned process-image relocation mutation without PE execution.
- `bin/simple test test/lib/common/wine_process_session_tls_dispatch_spec.spl --mode=interpreter --clean`: covers REQ-037 loader-owned TLS callback dispatch recording and empty-table handling.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl --mode=interpreter --clean`: includes REQ-037 system coverage for mapped TLS callback dispatch recording without PE execution.
- `bin/simple test test/lib/common/wine_process_session_loader_state_spec.spl --mode=interpreter --clean`: covers REQ-038 modeled import-loader refcount release and missing-export rollback.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl --mode=interpreter --clean`: includes REQ-038 system coverage for modeled loader state without host DLL loading or PE execution.
- `bin/simple test test/lib/common/wine_process_session_import_transaction_spec.spl --mode=interpreter --clean`: covers REQ-039 loader-state-gated VMA import patch transactions.
- `bin/simple test test/lib/common/wine_process_session_import_transaction_rollback_spec.spl --mode=interpreter --clean`: covers REQ-039 rollback-before-patch rejection without crossing into the VMA write path.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_transaction_spec.spl --mode=interpreter --clean`: includes REQ-039 system coverage for composed loader state plus VMA patch evidence without host DLL loading or PE execution.
- `bin/simple test test/lib/common/wine_process_session_import_entrypoint_handoff_spec.spl --mode=interpreter --clean`: covers REQ-040 patched-image entrypoint handoff after the import loader VMA transaction.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_entrypoint_handoff_spec.spl --mode=interpreter --clean`: includes REQ-040 system coverage for non-executing patched-image entrypoint handoff.
- `bin/simple test test/lib/common/wine_x86_64_decode_spec.spl --mode=interpreter --clean`: covers RIP-relative indirect call decoding and thunk-RVA target extraction.
- `bin/simple test test/lib/common/wine_hello_exe_spec.spl --mode=interpreter --clean`: covers import-binding agreement against thunk RVAs.
- `bin/simple test test/lib/common/wine_process_session_known_console_spec.spl --mode=interpreter --clean`: keeps known-console process execution on the patched-image path.
- `bin/simple test test/lib/common/wine_process_session_mapped_image_spec.spl --mode=interpreter --clean`: covers the mapped patched-image preflight and missing CPU evidence rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl --mode=interpreter --clean`: includes REQ-026 mapped patched process image coverage.
- `bin/simple test test/lib/common/wine_process_session_vma_thunk_write_spec.spl --mode=interpreter --clean`: covers the bounded process VMA write window for known thunk records.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.spl --mode=interpreter --clean`: includes REQ-027 bounded process VMA thunk patch window coverage.
- `bin/simple test test/lib/common/wine_process_session_full_image_handoff_spec.spl --mode=interpreter --clean`: covers the full-Wine image-to-VM handoff and rejection gates.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl --mode=interpreter --clean`: includes REQ-028 arbitrary process image VM handoff coverage.

Conservative boundary: this is a curated KERNEL32 table and bounded loader
sequence. It is not arbitrary DLL loading, host DLL mapping, Windows DLL search
order, arbitrary import-table binding, writable arbitrary OS VMA mutation beyond
the currently modeled thunk slots, PE DLL relocation, TLS initialization,
host-backed loader state, DLL entrypoint execution, TLS callback instruction
execution, or broad Win32/NT behavior.

## Completion Decision

The WM/VM prerequisite plan in `doc/03_plan/agent_tasks/simpleos_wine_wm_vm_execution_plan_2026-05-06.md` is implemented at the Wine-facing SimpleOS contract level. Modeled X11/VM gates are no longer accepted as production evidence, and the new production gates require SimpleOS window records, framebuffer presents, OS process/address-space identity, container namespace evidence, OS VMA image mapping, thread stack/guard setup, fault evidence, and no-host-code-jump policy.

This is still not a complete upstream Wine port. Full Wine graphics driver integration, compositor event-loop delivery, kernel page-table enforcement, broader POSIX/thread/dynload/service/peripheral behavior, arbitrary PE loading, broad x86_64 execution, and general NT/Win32 dispatch remain intentionally blocked outside these controlled prerequisite and GUI milestone slices.

## 2026-05-07 DllMain PEB/TEB Write-Handoff Update

`wine_dllmain_handoff_require_peb_teb_writes(...)` now composes PEB/TEB
loader-lock startup readiness with PEB, TEB, TLS-vector, and
process-parameter writable-page evidence before a retained DLL view can report
non-executing DllMain process-attach handoff readiness. A missing writable
startup mapping blocks the handoff before any DllMain execution claim.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: covers loader-lock plus PEB/TEB write readiness and unmapped startup-write rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level DllMain handoff requiring PEB/TEB writes.

## 2026-05-07 DllMain Startup-Fault Write-Handoff Update

`wine_dll_record_file_view_startup_fault_with_peb_teb_writes(...)` now carries
the write-gated DllMain handoff into the modeled SEH rollback path. Startup
rollback is recorded only after PEB/TEB loader-lock and writable-page evidence
are ready; missing startup writes block before rollback evidence is emitted.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: covers write-gated startup rollback and unmapped PEB/TEB write rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level startup rollback path requiring PEB/TEB writes.

## 2026-05-07 PEB/TEB Layout-Write Plan Update

`wine_peb_teb_layout_write_plan(...)` now turns PEB/TEB writable-page readiness
into bounded x64 startup layout records. The plan covers TEB stack bounds,
TEB TLS vector and PEB pointers, plus PEB image-base and process-parameter
pointers. Failed VM write readiness blocks layout planning before any record is
reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_peb_teb_spec.spl --mode=interpreter --clean`: covers successful x64 layout record planning and write-readiness rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level PEB/TEB layout-write plan.

## 2026-05-07 NTDLL PEB/TEB Layout-Handoff Update

`wine_ntdll_execute_process_info_with_peb_teb_layout(...)` now requires the
six-record PEB/TEB layout-write plan before the NTDLL process/thread
information bridge reports PEB and TEB addresses. Failed layout planning
propagates as a hard handoff rejection.

Fresh evidence:

- `bin/simple test test/lib/common/wine_ntdll_process_info_spec.spl --mode=interpreter --clean`: covers layout-aware NTDLL process-info handoff and layout rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level PEB/TEB layout-to-NTDLL handoff.

## 2026-05-07 DllMain PEB/TEB Layout-Handoff Update

`wine_dllmain_handoff_require_peb_teb_layout(...)` now requires the six-record
PEB/TEB layout-write plan before a retained DLL view can report non-executing
DllMain process-attach handoff readiness. Failed layout planning blocks the
handoff before any DllMain execution claim.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: covers layout-gated DllMain handoff and layout rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level DllMain layout handoff.

## 2026-05-07 DllMain Startup-Fault Layout-Handoff Update

`wine_dll_record_file_view_startup_fault_with_peb_teb_layout(...)` now carries
the layout-gated DllMain handoff into the modeled SEH rollback path. Startup
rollback is recorded only after loader-lock readiness and the six-record
PEB/TEB layout-write plan are ready.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: covers layout-gated startup rollback and layout rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level startup rollback path requiring the PEB/TEB layout handoff.

## 2026-05-07 PEB/TEB Layout Byte-Payload Update

`wine_peb_teb_layout_byte_writes(...)` now materializes the six PEB/TEB x64
layout records as bounded little-endian 8-byte payloads. This is still modeled
payload evidence only; it does not claim live VM memory mutation.

Fresh evidence:

- `bin/simple test test/lib/common/wine_peb_teb_spec.spl --mode=interpreter --clean`: covers successful layout byte payload generation and layout rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level layout byte payload handoff.

## 2026-05-07 PEB/TEB VM Byte-Write Readback Update

`wine_vm_write_bytes(...)` and `wine_vm_read_bytes(...)` now model committed
VM byte writes and readback with permission and region-boundary checks.
`wine_peb_teb_apply_layout_byte_writes(...)` composes the PEB/TEB layout
payloads through that VM byte ledger and verifies readback before reporting
VM-backed startup mutation evidence.

Fresh evidence:

- `bin/simple test test/lib/common/wine_vm_adapter_spec.spl --mode=interpreter --clean`: covers modeled VM byte write/readback and write rejection.
- `bin/simple test test/lib/common/wine_peb_teb_spec.spl --mode=interpreter --clean`: covers PEB/TEB layout byte application plus read-only startup-memory rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level PEB/TEB VM byte-write/readback path.

## 2026-05-07 NTDLL PEB/TEB VM-Write Handoff Update

`wine_ntdll_execute_process_info_with_peb_teb_vm_writes(...)` now requires the
PEB/TEB VM byte-write/readback result before the NTDLL process/thread
information bridge reports PEB and TEB addresses. Failed VM byte-write
composition propagates as a hard handoff rejection.

Fresh evidence:

- `bin/simple test test/lib/common/wine_ntdll_process_info_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated process-info handoff and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level VM-write/readback-to-NTDLL handoff.

## 2026-05-07 DllMain PEB/TEB VM-Write Handoff Update

`wine_dllmain_handoff_require_peb_teb_vm_writes(...)` now requires PEB/TEB VM
byte-write/readback evidence before a retained DLL view can report
non-executing DllMain process-attach handoff readiness. Failed VM byte-write
composition blocks the handoff before any DllMain execution claim and clears
mapped base, mapped size, entrypoint, callback, and dispatch counts.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated DllMain handoff, failure propagation, and stale mapped-state clearing.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level DllMain VM-write/readback handoff before carrying mapped state.

## 2026-05-07 DllMain Startup-Fault VM-Write Handoff Update

`wine_dll_record_file_view_startup_fault_with_peb_teb_vm_writes(...)` now
carries the VM byte-write/readback-gated DllMain handoff into the modeled SEH
rollback path. Startup rollback is recorded only after loader-lock readiness
and PEB/TEB VM write/readback evidence are ready.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated startup rollback and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_startup_fault_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level startup rollback path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 Process Entrypoint Startup-Fault VM-Write Handoff Update

`wine_process_record_imported_entrypoint_startup_fault_with_peb_teb_vm_writes(...)`
now requires PEB/TEB VM byte-write/readback evidence before the imported
process-entrypoint startup rollback path can record non-executing SEH rollback
evidence. Failed VM byte-write composition propagates as a hard handoff
rejection before rollback is recorded. The prebuilt-handoff overload now clears
mapped base, mapped size, entrypoint, and module counts on VM-write rejection so
startup-fault handling cannot carry stale mapped-state evidence.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_entrypoint_startup_fault_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated imported entrypoint rollback, failure propagation, and stale mapped-state clearing.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level imported entrypoint rollback path requiring PEB/TEB VM write/readback evidence before carrying mapped state.

Performance follow-up: the imported-entrypoint startup fault specs remain near
the 60s interpreter watchdog because the import-binding fixture is expensive;
split the heavy PE import-binding coverage from handoff-level rollback gates
before adding more examples to this spec.

## 2026-05-07 Full Image Handoff VM-Write Update

`wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(...)` now
requires PEB/TEB VM byte-write/readback evidence before full-image validation,
mapping, or handoff evidence can be produced. Failed VM byte-write composition
returns zero mapped/entry addresses and a non-executing rejection; successful
readback prefixes the handoff evidence before reporting readiness.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_full_image_handoff_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated full-image handoff and pre-mapping rejection with zero mapped/entry addresses.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level full-image handoff path requiring PEB/TEB VM write/readback evidence before image mapping.

## 2026-05-07 Full Image Loader Runtime VM-Write Update

`wine_process_plan_full_image_loader_runtime_with_peb_teb_vm_writes(...)` now
starts from the PEB/TEB VM byte-write/readback-gated full-image handoff before
recording relocation and TLS runtime preflight evidence. Failed VM byte-write
composition blocks the runtime preflight before relocation/TLS evidence is
reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_loader_runtime_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated full-image loader runtime planning and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level loader runtime path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 Loader Relocation VMA VM-Write Update

`wine_process_apply_loader_relocations_in_vma_with_peb_teb_vm_writes(...)` now
requires the PEB/TEB VM byte-write/readback-gated loader runtime preflight
before opening the modeled relocation write window. Failed VM byte-write
composition blocks relocation mutation before copied image bytes are patched.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_vma_relocation_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated loader relocation mutation and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level relocation mutation path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 TLS Callback Dispatch VM-Write Update

`wine_process_record_tls_callback_dispatch_with_peb_teb_vm_writes(...)` now
requires the PEB/TEB VM byte-write/readback-gated relocation path before
recording loader-owned TLS callback dispatch evidence. Failed VM byte-write
composition blocks dispatch evidence before TLS callback handoff is reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_tls_dispatch_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated TLS callback dispatch and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level TLS callback dispatch path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 Import Thunk Planning VM-Write Update

`wine_process_plan_import_thunk_patches_with_peb_teb_vm_writes(...)` now
requires the PEB/TEB VM byte-write/readback-gated TLS dispatch path before
recording guarded KERNEL32 import-thunk planning evidence. Failed VM byte-write
composition blocks import-thunk planning before thunk-binding evidence is
reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_thunk_load_bind_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated import thunk planning and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_thunk_load_bind_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level import thunk planning path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 Import Thunk VMA VM-Write Update

`wine_process_apply_known_kernel32_thunk_patches_in_vma_with_peb_teb_vm_writes(...)`
now requires the PEB/TEB VM byte-write/readback-gated TLS dispatch path before
opening the modeled KERNEL32 import-thunk VMA write window. Failed VM
byte-write composition blocks VMA thunk mutation before copied image bytes are
patched. TLS preflight and record-planning rejection now return no patched
image, no mapped region, and explicit no-VMA-write evidence.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_vma_thunk_write_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated VMA import thunk mutation plus no-patched-image rejection before VMA thunk writes.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level VMA import thunk write path requiring PEB/TEB VM write/readback evidence and no-image rejection before VMA thunk writes.

## 2026-05-07 Mapped Image VM-Write Update

`wine_process_map_known_console_image_with_peb_teb_vm_writes(...)` now requires
the PEB/TEB VM byte-write/readback-gated import-thunk VMA write path before a
known-console image can report mapped-image preflight readiness. Failed VM
byte-write composition blocks mapped-image readiness before CPU dispatch
preflight is reported. Missing CPU evidence now returns no mapped image, no
mapped region, and explicit no-arbitrary-execution evidence before VM-gated or
plain mapped-image preflight can proceed.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_mapped_image_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated mapped-image preflight, failure propagation, and no-mapped-image CPU evidence rejection.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level mapped-image path requiring PEB/TEB VM write/readback evidence and rejecting missing CPU evidence without mapped image state.

## 2026-05-07 CPU Dispatch Preflight VM-Write Update

`wine_process_cpu_dispatch_preflight_with_peb_teb_vm_writes(...)` now requires
the PEB/TEB VM byte-write/readback-gated mapped-image path before reporting CPU
dispatch preflight readiness. Failed VM byte-write composition blocks CPU
dispatch preflight before known-console dispatch planning is reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_cpu_preflight_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated CPU dispatch preflight and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level CPU dispatch preflight path requiring PEB/TEB VM write/readback evidence.

Performance follow-up: `test/lib/common/wine_process_session_spec.spl` now
passes after moving known-console dispatch coverage into a focused spec, but it
still runs near the 60s interpreter watchdog. Split the remaining import and
CPU preflight examples into focused specs before adding more coverage to the
aggregate session-planning spec.

## 2026-05-07 Known-Console Dispatch VM-Write Update

`wine_process_plan_known_console_dispatch_with_peb_teb_vm_writes(...)` now
requires the PEB/TEB VM byte-write/readback-gated mapped-image path before a
known-console dispatch plan can be decoded. Failed VM byte-write composition
blocks dispatch planning before instruction decoding is reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_known_console_dispatch_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated known-console dispatch planning and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_known_console_dispatch_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level known-console dispatch path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 Known-Console Execution VM-Write Update

`wine_process_execute_known_console_with_peb_teb_vm_writes(...)` now requires
the PEB/TEB VM byte-write/readback-gated mapped-image path before the bounded
known-console execution helper can run the modeled NT bridge plan. Failed VM
byte-write composition blocks known-console execution before stdout/exit-code
evidence is reported.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_known_console_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated known-console execution and failure propagation.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level known-console execution path requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 Imported Entrypoint Handoff VM-Write Update

`wine_process_prepare_imported_entrypoint_handoff_with_peb_teb_vm_writes(...)`
now requires PEB/TEB VM byte-write/readback evidence before exposing the
imported process-entrypoint handoff. The process startup-fault VM-write wrapper
now consumes that gated handoff path before non-executing SEH rollback can be
recorded. Failed VM byte-write composition rejects the handoff before startup
fault evidence is considered.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_import_entrypoint_handoff_vm_write_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated imported entrypoint handoff.
- `bin/simple test test/lib/common/wine_process_session_import_entrypoint_handoff_vm_write_failure_spec.spl --mode=interpreter --clean`: covers VM-write/readback failure propagation before imported entrypoint handoff readiness.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_entrypoint_handoff_vm_write_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level imported entrypoint handoff requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 DllMain Prepare VM-Write Handoff Update

`wine_dll_prepare_file_view_dllmain_handoff_with_peb_teb_vm_writes(...)` now
routes retained DllMain process-attach handoff preparation through the
VM-readback import-binding record before exposing handoff readiness. The
DllMain startup-fault VM-write wrapper now consumes that gated handoff path
before non-executing SEH rollback can be recorded.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_dllmain_handoff_vm_write_spec.spl --mode=interpreter --clean`: covers retained DllMain handoff preparation consuming the VM-readback import-binding record.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_dllmain_handoff_vm_write_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level retained DllMain handoff consuming VM-readback import binding evidence.

## 2026-05-07 Import-Loader Transaction VM-Write Update

`wine_process_apply_import_loader_transaction_in_vma_with_peb_teb_vm_writes(...)`
now requires PEB/TEB VM byte-write/readback evidence before descriptor-qualified
import-loader VMA patching can complete. The imported-entrypoint VM-write
handoff now consumes this gated import-loader transaction path instead of
gating only after transaction readiness was already reported. Failed VM-write
evidence and descriptor planning rejection return no patched image, no mapped
region, and explicit no-VMA-write evidence.

Fresh evidence:

- `bin/simple test test/lib/common/wine_process_session_import_descriptor_vma_vm_write_spec.spl --mode=interpreter --clean`: covers VM-write and descriptor-planning rejection returning no patched image, no mapped region, and no VMA thunk-write evidence.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_descriptor_vma_vm_write_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level descriptor VMA VM-write and descriptor-planning rejection before VMA thunk writes.
- `bin/simple test test/lib/common/wine_process_session_import_loader_transaction_rejection_spec.spl --mode=interpreter --clean`: covers import-loader transaction aborts returning no patched image and no VMA thunk-write evidence.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_loader_transaction_rejection_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level transaction abort boundary before patched image exposure.
- `bin/simple test test/lib/common/wine_process_session_import_transaction_vm_write_spec.spl --mode=interpreter --clean`: verifies the transaction path still composes the VM-readback-gated descriptor patch path.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_process_import_loader_transaction_vm_write_spec.spl --mode=interpreter --clean`: verifies the SimpleOS transaction path still composes the VM-readback-gated descriptor patch path.

Performance follow-up: the focused import-loader transaction and imported
entrypoint VM-write specs pass but run close to the 60s interpreter watchdog.
Split or optimize the shared multi-DLL PE fixture path before adding more
examples to these specs.

## 2026-05-07 DLL TLS Dispatch VM-Write Update

`wine_dll_record_file_view_tls_dispatch_with_peb_teb_vm_writes(...)` now
requires PEB/TEB VM byte-write/readback evidence before retained DLL view TLS
callback dispatch readiness can be recorded. The path remains non-executing:
TLS callback instructions, DllMain, and arbitrary PE code are still not run.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_tls_dispatch_vm_write_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated retained DLL TLS dispatch readiness.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_tls_dispatch_vm_write_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level retained DLL TLS dispatch requiring PEB/TEB VM write/readback evidence.

## 2026-05-07 DLL Import Binding VM-Write Update

`wine_dll_bind_file_view_imports_with_peb_teb_vm_writes(...)` now requires
PEB/TEB VM byte-write/readback evidence before retained DLL import binding can
report modeled IAT patch readiness. The retained DLL TLS-dispatch VM-write path
now consumes this gated import-binding record instead of applying a duplicate
gate after import binding.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_import_binding_vm_write_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated retained DLL import binding readiness.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_import_binding_vm_write_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level retained DLL import binding requiring PEB/TEB VM write/readback evidence.
- `bin/simple test test/lib/common/wine_dll_view_tls_dispatch_vm_write_spec.spl --mode=interpreter --clean`: verifies the TLS-dispatch VM path still passes through the gated import-binding record.

## 2026-05-07 DLL Relocation VM-Write Update

`wine_dll_apply_file_view_relocations_with_peb_teb_vm_writes(...)` now requires
PEB/TEB VM byte-write/readback evidence before retained DLL file-view relocation
readiness can be reported. The retained DLL import-binding VM-write path now
consumes this gated relocation record instead of gating only after relocation
readiness was already available.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_view_relocation_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated retained DLL relocation readiness alongside existing relocation behavior.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level retained DLL relocation requiring PEB/TEB VM write/readback evidence.
- `bin/simple test test/lib/common/wine_dll_view_import_binding_vm_write_spec.spl --mode=interpreter --clean`: verifies import binding still passes through the gated relocation record.

## 2026-05-07 DLL File-View Mapping VM-Write Update

`wine_dll_map_file_backed_view_with_peb_teb_vm_writes(...)` now requires PEB/TEB
VM byte-write/readback evidence before retained DLL file-view mapping readiness
can be reported. The retained DLL relocation VM-write path now consumes this
gated file-view mapping record instead of gating only after mapping readiness
was already available.

Fresh evidence:

- `bin/simple test test/lib/common/wine_dll_file_view_spec.spl --mode=interpreter --clean`: covers VM-write/readback-gated retained DLL file-view mapping alongside existing file-view behavior.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_dll_file_view_spec.spl --mode=interpreter --clean`: covers the SimpleOS system-level retained DLL file view requiring PEB/TEB VM write/readback evidence.
- `bin/simple test test/lib/common/wine_dll_view_relocation_spec.spl --mode=interpreter --clean`: verifies retained DLL relocation still passes through the gated file-view mapping record.
