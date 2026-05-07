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
| SimpleOS executable environment gate | `src/lib/common/wine_simpleos_exec_env_gate.spl` requires QEMU VM, full OS boot, user process, VM space, filesystem, window system, network, container namespace, and container rootfs evidence; `src/lib/common/wine_substrate.spl` exposes this as the `exec_env` matrix row/gate | Implemented prerequisite |
| Dynamic loading prerequisite | `src/lib/common/wine_dynload_adapter.spl` requires native loader APIs, search path/dependency/namespace coverage, relocation/import/TLS surfaces, structured loader errors, and bounded NTDLL `LdrLoadDll`/`LdrGetProcedureAddress`/`LdrUnloadDll` evidence before dynload readiness | Implemented prerequisite |
| Thread/TLS/wait prerequisite | `src/lib/common/wine_thread_adapter.spl` requires thread/TLS/synchronization/wait/fault APIs and bounded NT `CreateThread`/`WaitForSingleObject` evidence before pthread readiness | Implemented prerequisite |
| WM/graphics production prerequisite | `src/lib/common/ui/wine_simpleos_window_bridge.spl` creates SimpleOS `/win` `WindowRecord` state and framebuffer present evidence; `src/lib/common/ui/wine_x11_adapter.spl` requires that bridge through `wine_x11_backend_production_ready` | Implemented prerequisite |
| VM/container production prerequisite | `src/lib/common/wine_vm_adapter.spl` distinguishes modeled spaces from OS process/address-space/container-backed spaces; `src/lib/common/wine_image_vm_map.spl` maps validated PE images plus stack/guard before execution | Implemented prerequisite |
| PE/COFF and CPU preparation | `src/lib/common/wine_pe_gate.spl`, `src/lib/common/pe_coff_header.spl`, `src/lib/common/wine_pe_loader_runtime.spl`, `src/lib/common/wine_image_map.spl`, `src/lib/common/wine_x86_64_decode.spl`, and `src/lib/common/wine_cpu_exec.spl` validate image layout, entry windows, imports, relocation/TLS readiness, decoded call targets, safe prologues, and dispatch evidence before controlled execution | Verified for controlled hello path |
| NT bridge and dispatch sequence | `src/lib/common/wine_nt_bridge.spl` and `src/lib/common/wine_hello_dispatch.spl` execute only the decoded-plan `GetStdHandle`, `WriteFile`, `ExitProcess` sequence with stdout handle, byte-count, payload RVA, and exit-code evidence | Verified for controlled hello path |
| Known non-GUI `hello.exe` command | `src/app/wine_hello/main.spl` prints `Hello from SimpleOS Wine` through OS-backed VM image mapping, composed manifest, PE validation, import binding, CPU plan, NT bridge, and decoded stdout payload path | Verified |
| Controlled GUI hello milestone | `src/lib/common/wine_gui_hello.spl` and `src/app/wine_gui_hello/main.spl` require the VM-backed PE hello path, then bind Wine-facing X11 state to SimpleOS `/win` framebuffer evidence before reporting window title/text/checksum | Verified |
| Unsupported programs stay blocked | Tests cover malformed PE, missing gates, unsupported imports, import/CPU target mismatch, missing stdout payload, missing decoder/dispatch evidence, reordered/missing/extra bridge calls, and unsupported/truncated x86_64 instructions | Verified for listed blockers |
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

## 2026-05-07 Executable-Environment Matrix Update

The top-level Wine substrate matrix now exposes the SimpleOS executable-environment gate directly through `wine_substrate_exec_env_gate` and the `exec_env` capability row. This makes VM/full-OS/container evidence a first-class Wine readiness prerequisite instead of an implicit side gate.

Fresh evidence:

- `bin/simple check src/lib/common/wine_substrate.spl test/lib/common/wine_substrate_spec.spl doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: all checks passed.
- `bin/simple test test/lib/common/wine_substrate_spec.spl`: 16 examples, 0 failures.
- `bin/simple test test/lib/common/wine_simpleos_exec_env_gate_spec.spl`: 5 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`: 14 examples, 0 failures.

Conservative boundary: `exec_env=verified` means the controlled Wine path has explicit SimpleOS VM/full-OS/container evidence. It does not by itself imply a complete Wine port or arbitrary PE compatibility.

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

## Completion Decision

The WM/VM prerequisite plan in `doc/03_plan/agent_tasks/simpleos_wine_wm_vm_execution_plan_2026-05-06.md` is implemented at the Wine-facing SimpleOS contract level. Modeled X11/VM gates are no longer accepted as production evidence, and the new production gates require SimpleOS window records, framebuffer presents, OS process/address-space identity, container namespace evidence, OS VMA image mapping, thread stack/guard setup, fault evidence, and no-host-code-jump policy.

This is still not a complete upstream Wine port. Full Wine graphics driver integration, compositor event-loop delivery, kernel page-table enforcement, broader POSIX/thread/dynload/service behavior, arbitrary PE loading, broad x86_64 execution, and general NT/Win32 dispatch remain intentionally blocked outside these controlled prerequisite and GUI milestone slices.
