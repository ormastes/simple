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
| WM/graphics production prerequisite | `src/lib/common/ui/wine_simpleos_window_bridge.spl` creates SimpleOS `/win` `WindowRecord` state and framebuffer present evidence; `src/lib/common/ui/wine_x11_adapter.spl` requires that bridge through `wine_x11_backend_production_ready` | Implemented prerequisite |
| VM/container production prerequisite | `src/lib/common/wine_vm_adapter.spl` distinguishes modeled spaces from OS process/address-space/container-backed spaces; `src/lib/common/wine_image_vm_map.spl` maps validated PE images plus stack/guard before execution | Implemented prerequisite |
| PE/COFF and CPU preparation | `src/lib/common/wine_image_map.spl`, `src/lib/common/wine_x86_64_decode.spl`, and `src/lib/common/wine_cpu_exec.spl` validate image layout, entry windows, decoded call targets, safe prologues, and dispatch evidence before controlled execution | Verified for controlled hello path |
| NT bridge and dispatch sequence | `src/lib/common/wine_nt_bridge.spl` and `src/lib/common/wine_hello_dispatch.spl` execute only the ordered `GetStdHandle`, `WriteFile`, `ExitProcess` sequence with stdout handle, byte-count, payload RVA, and exit-code evidence | Verified for controlled hello path |
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

## Completion Decision

The WM/VM prerequisite plan in `doc/03_plan/agent_tasks/simpleos_wine_wm_vm_execution_plan_2026-05-06.md` is implemented at the Wine-facing SimpleOS contract level. Modeled X11/VM gates are no longer accepted as production evidence, and the new production gates require SimpleOS window records, framebuffer presents, OS process/address-space identity, container namespace evidence, OS VMA image mapping, thread stack/guard setup, fault evidence, and no-host-code-jump policy.

This is still not a complete upstream Wine port. Full Wine graphics driver integration, compositor event-loop delivery, kernel page-table enforcement, broader POSIX/thread/dynload/service behavior, arbitrary PE loading, broad x86_64 execution, and general NT/Win32 dispatch remain intentionally blocked outside these controlled prerequisite and GUI milestone slices.
