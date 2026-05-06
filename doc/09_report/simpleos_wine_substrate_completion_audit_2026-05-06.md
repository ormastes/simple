# Completion Audit: SimpleOS Wine Substrate

Date: 2026-05-06

## Objective Restated

Deliver a Wine-support path for SimpleOS:

1. research Wine-needed features in SimpleOS and Simple lib;
2. improve 2D rendering and WM toward X11-class backend behavior;
3. extend VM/container support for Wine-level memory behavior;
4. cover remaining Wine host substrate features;
5. base the host wait/I/O substrate on `nogc_async_mut`;
6. then run a non-GUI `hello.exe`;
7. use the design and implementation workflows.

## Prompt-To-Artifact Checklist

| Requirement | Evidence | Status |
| --- | --- | --- |
| Wine research | `doc/01_research/local/simpleos_wine_support.md`, `doc/01_research/domain/simpleos_wine_support.md`, `doc/09_report/simpleos_wine_support_research_2026-05-06.md` | Done |
| Design/impl workflow checked | `.codex/skills/design/SKILL.md`, `.codex/skills/impl/SKILL.md` inspected; prerequisite artifacts created | Done |
| Requirements | `doc/02_requirements/feature/simpleos_wine_substrate.md`, `doc/02_requirements/nfr/simpleos_wine_substrate.md` | Done |
| Architecture/design | `doc/04_architecture/simpleos_wine_substrate.md`, `doc/05_design/simpleos_wine_substrate.md` | Done |
| System test plan/spec | `doc/03_plan/sys_test/simpleos_wine_substrate.md`, `doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl` | Done |
| Agent task breakdown | `doc/03_plan/agent_tasks/simpleos_wine_substrate.md` | Done |
| Phase 0 capability gate | `src/lib/common/wine_substrate.spl`, `test/lib/common/wine_substrate_spec.spl`; process-backed evidence now requires Browser Demo, Hello World, Editor, Terminal, and File Manager markers; capability rows expose state, implementation path, evidence command, and notes derived from explicit gate evidence; matrix rows explicitly include filesystem semantics, IPC/waits, audio, fonts, and input instead of hiding them under host | Done |
| 2D renderer/WM X11-class implementation | Requirements and gates exist; `src/lib/common/ui/x11_backend_gate.spl` adds a native X11-class readiness contract; `src/lib/common/ui/wine_x11_adapter.spl` adds a verified modeled backend state for display/screen, window lifecycle, surface/damage/expose/present, input/focus, cursor, clipboard, text/glyph, blit, and fill evidence; final renderer/WM and Wine graphics driver are not complete | Partial |
| VM/container Wine-level implementation | Requirements and gates exist; `src/lib/common/wine_vm_gate.spl` adds a Wine-level VM/container readiness contract; `src/lib/common/wine_vm_adapter.spl` adds a verified modeled address-space adapter for reserve, fixed-map conflict detection, commit, protect, guard-page, unmap, user-pointer lookup, access-fault classification, and fault evidence; kernel VMM/container implementation is not complete | Partial |
| Remaining POSIX/thread/dynload/audio/font/input features | `src/lib/common/wine_host_gate.spl` adds host-substrate readiness contract; `src/lib/common/wine_posix_adapter.spl` adds a verified fd/process/stdio/timer/socket/path/errno adapter contract over `nogc_async_mut` completion and event-loop prerequisites; `src/lib/common/wine_thread_adapter.spl` maps existing thread/mutex/condvar SFFI and keeps TLS, semaphore, event wait objects, and thread-fault records as explicit blockers; `src/lib/common/wine_dynload_adapter.spl` separates native `dlopen`/`dlsym` support from Wine-ready search-path, dependency, namespace, relocation, import, TLS-callback, PE-boundary, and structured-error behavior; `src/lib/common/wine_service_adapter.spl` adds a verified service contract for IPC, handles, audio, fonts, crypto, HID, printing, and multimedia; final syscall/device implementations are not complete | Partial |
| `nogc_async_mut` async substrate | `src/lib/common/wine_async_gate.spl` adds an explicit gate for `Future`, `Poll`, `Waker`, `IoDriver`, `EventLoop`, completion polling, and noalloc capability prerequisites | Partial |
| PE/COFF loader preparation | `src/lib/common/wine_pe_gate.spl` adds readiness contract; `src/lib/common/pe_coff_header.spl` adds a safe header classifier, section-table bound check, section raw/virtual bound validation, executable entry-section validation, RVA-to-file mapping, data-directory check, first import descriptor-name validation, null import-descriptor terminator validation, mapped relocation/TLS directory validation, first thunk table validation before symbol extraction, first thunk symbol extraction, first thunk name-RVA binding extraction, and entry/image-size readers; `src/lib/common/wine_image_map.spl` additionally verifies that the CPU entry scan window is mapped and contiguous before decode; full loader/executor not complete | Partial |
| Known non-GUI `hello.exe` fixture | `src/lib/common/wine_hello_exe.spl` blocks on missing gates including `nt_bridge=verified`, rejects malformed PE bytes, validates mapped relocation/TLS directories, checks minimal `KERNEL32.dll` imports, requires a terminated import descriptor and valid first import thunk table before symbol extraction, checks expected imported-name RVA bindings through `src/lib/common/wine_nt_api_catalog.spl` and the structured binding plan in `src/lib/common/wine_nt_import.spl`, validates image-layout readiness including bounded sections and executable entry section through `src/lib/common/wine_image_map.spl`, derives a CPU-level execution plan through `src/lib/common/wine_cpu_exec.spl`, decodes a tiny x86_64 hello call skeleton into a structured instruction plan with known relative targets plus supported/unsupported/truncated instruction classification, bounded instruction lengths, and a bounded scan-window result for unsupported, truncated, overrun, and instruction-limit failures through `src/lib/common/wine_x86_64_decode.spl`, including common `sub/add rsp, imm8`, `nop`, and `ret` forms, verifies the import binding plan and CPU execution plan agree, resolves concrete milestone NT calls with stdout handle, byte-count, and exit-code evidence through `src/lib/common/wine_nt_api_catalog.spl` and `src/lib/common/wine_nt_bridge.spl`, dispatches the modeled `GetStdHandle`, `WriteFile`, and `ExitProcess` sequence through an ordered bridge executor, and executes only a marked `SIMPLE_WINE_HELLO` fixture by passing the CPU plan into `src/lib/common/wine_hello_dispatch.spl`; `src/app/wine_hello/main.spl` now routes through the composed precondition manifest before adding CPU/dispatch evidence; arbitrary PE execution remains missing | Verified for known fixture |
| NT/Win32 API catalog | `src/lib/common/wine_nt_api_catalog.spl` records the implemented hello API set separately from catalogued future `kernel32.dll` and `ntdll.dll` memory, file, thread/wait, heap, and process-environment calls. Import and bridge gates reject unknown or catalogued calls instead of treating catalog entries as arbitrary PE-dispatchable; `wine_nt_bridge_modeled_precondition_gate` separately verifies that catalogued precondition symbols route to modeled precondition contracts; `src/lib/common/wine_nt_bridge.spl` now executes stdout only through the ordered `GetStdHandle`, `WriteFile`, `ExitProcess` bridge sequence. | Verified as boundary contract |
| NT virtual memory bridge | `src/lib/common/wine_nt_virtual_memory.spl` models `VirtualAlloc`, `VirtualProtect`, and `VirtualFree` over `src/lib/common/wine_vm_adapter.spl`, including automatic/fixed allocation, overlap rejection, protection changes with old permissions, free/unmap, and invalid target errors. These calls remain non-dispatchable for arbitrary PE imports. | Verified as modeled precondition |
| NT file I/O bridge | `src/lib/common/wine_nt_file_io.spl` models `CreateFileW`, `ReadFile`, and `CloseHandle` over the POSIX/`nogc_async_mut` adapter contract, including POSIX readiness blocking, modeled file open, read cursor advancement, close, invalid handle, missing file, invalid path, and invalid read-size errors. These calls remain non-dispatchable for arbitrary PE imports. | Verified as modeled precondition |
| NT thread/wait bridge | `src/lib/common/wine_nt_thread_wait.spl` models `CreateThread`, `WaitForSingleObject`, and `GetLastError` over the Wine thread adapter contract, including readiness blocking, modeled thread handles, wait completion, timeout, invalid entrypoints, invalid handles, and last-error reporting. These calls remain non-dispatchable for arbitrary PE imports. | Verified as modeled precondition |
| NT process environment bridge | `src/lib/common/wine_nt_process_env.spl` models `GetCommandLineW` and `GetEnvironmentStringsW` over the POSIX/`nogc_async_mut` argv/env contract, including POSIX readiness blocking, argv0 validation, command-line quoting, deterministic environment-block formatting, and invalid environment-key errors. These calls remain non-dispatchable for arbitrary PE imports. | Verified as modeled precondition |
| NT heap bridge | `src/lib/common/wine_nt_heap.spl` models `HeapAlloc` and `HeapFree` with a deterministic process-heap handle, VM-reservation-backed block tracking, invalid-handle and invalid-size checks, unknown-pointer rejection, and double-free detection. These calls remain non-dispatchable for arbitrary PE imports. | Verified as modeled precondition |
| ntdll/Rtl bridge | `src/lib/common/wine_ntdll_bridge.spl` maps `NtAllocateVirtualMemory`, `NtProtectVirtualMemory`, `NtFreeVirtualMemory`, `NtCreateFile`, `NtReadFile`, `NtClose`, `RtlAllocateHeap`, and `RtlFreeHeap` onto the modeled VM, file, close, and heap precondition bridges while preserving underlying readiness failures. These calls remain non-dispatchable for arbitrary PE imports. | Verified as modeled precondition |
| Composed precondition manifest | `src/lib/common/wine_precondition_manifest.spl` composes process, VM, renderer, host, POSIX, pthread, dynamic loading, async, PE-loader, NT bridge, and hello.exe gate states into a single ordered decision; it blocks incomplete process evidence before any proxy gate and blocks `hello.exe` until `nt_bridge=verified` | Verified as manifest |
| Fixture manifest builder | `src/lib/common/wine_precondition_fixture_builder.spl` derives the known fixture manifest from adapter/gate modules instead of literal ready strings | Verified as integration |
| CPU/dispatch evidence | `src/lib/common/wine_cpu_exec.spl` exposes structured execution evidence for thread-context facets covering RIP/RSP/register initialization/TEB binding, user-stack facets covering allocation/commit/guard page/alignment, entrypoint-mapping facets covering valid RVA/executable section/readable entry window, concrete import-thunk binding facets for valid thunk tables, resolved symbols, matched bindings, and guarded IAT, stdout handle facets for std-output identity, writable handle, byte-count agreement, and guarded writes, exit-trap facets for process exit, status code, and no fallthrough, no-native-jump facets for import targets, entry bounds, and blocked host-code jumps, concrete Win64 ABI facets for register args, shadow space, stack alignment, return values, and guarded calls, concrete x86_64 decoder facets for mapped/bounded decode windows, supported ops, and call targets, plus concrete x86_64 dispatch facets for no-native-jump dispatch, import-only calls, exit trapping, and stdout sequencing; it also routes the hello CPU plan through a mapped contiguous image-window gate and bounded x86_64 entry scan before accepting dispatch; `wine_hello_exe_probe_manifest_evidence` accepts this typed evidence on the manifest path. | Verified as modeled precondition |

## Verification Evidence

- `bin/simple test test/lib/common/wine_async_gate_spec.spl --mode=interpreter`: 4 examples, 0 failures.
- `bin/simple test test/lib/common/wine_substrate_spec.spl --mode=interpreter --clean`: 15 examples, 0 failures.
- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl --mode=interpreter --clean`: 13 examples, 0 failures.
- `bin/simple test test/lib/common/ui/x11_backend_gate_spec.spl --mode=interpreter`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/ui/wine_x11_adapter_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_vm_gate_spec.spl --mode=interpreter`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/wine_vm_adapter_spec.spl --mode=interpreter --clean`: 8 examples, 0 failures.
- `bin/simple test test/lib/common/wine_host_gate_spec.spl --mode=interpreter`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/wine_posix_adapter_spec.spl --mode=interpreter --clean`: 7 examples, 0 failures.
- `bin/simple test test/lib/common/wine_thread_adapter_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_dynload_adapter_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_service_adapter_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_precondition_manifest_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_precondition_fixture_builder_spec.spl --mode=interpreter --clean`: 3 examples, 0 failures.
- `bin/simple test test/lib/common/wine_pe_gate_spec.spl --mode=interpreter`: 7 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_import_spec.spl --mode=interpreter --clean`: 7 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_api_catalog_spec.spl --mode=interpreter --clean`: 7 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_virtual_memory_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_file_io_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_thread_wait_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_process_env_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_heap_spec.spl --mode=interpreter --clean`: 6 examples, 0 failures.
- `bin/simple test test/lib/common/wine_ntdll_bridge_spec.spl --mode=interpreter --clean`: 5 examples, 0 failures.
- `bin/simple test test/lib/common/wine_image_map_spec.spl --mode=interpreter --clean`: 7 examples, 0 failures.
- `bin/simple test test/lib/common/wine_cpu_exec_spec.spl --mode=interpreter --clean`: 15 examples, 0 failures.
- `bin/simple test test/lib/common/wine_x86_64_decode_spec.spl --mode=interpreter --clean`: 13 examples, 0 failures.
- `bin/simple test test/lib/common/wine_nt_bridge_spec.spl --mode=interpreter --clean`: 12 examples, 0 failures.
- `bin/simple test test/lib/common/wine_hello_dispatch_spec.spl --mode=interpreter --clean`: 9 examples, 0 failures.
- `bin/simple test test/lib/common/wine_hello_exe_spec.spl --mode=interpreter --clean`: 14 examples, 0 failures.
- `bin/simple test test/lib/common/wine_hello_fixture_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple test test/lib/common/pe_coff_header_spec.spl --mode=interpreter --clean`: 14 examples, 0 failures.
- `bin/simple test test/integration/app/wine_hello_command_spec.spl --mode=interpreter --clean`: 1 example, 0 failures.
- `bin/simple run src/app/wine_hello/main.spl`: printed `Hello from SimpleOS Wine` and returned the modeled `ExitProcess(0)` exit code.
- `bin/simple check src/lib`: all checks passed, 2649 files.
- `bin/simple check src/app/wine_hello`: all checks passed, 1 file.

## Completion Decision

The overall objective is not complete as a general Wine port. Phase 0 is complete and verified, and the known non-GUI `hello.exe` milestone fixture now prints `Hello from SimpleOS Wine\n` only after PE validation, terminated import descriptor checks, mapped relocation/TLS directory checks, bounded section raw/virtual layout, executable entry-section checks, minimal import resolution with a structured binding plan, image-layout checks, a CPU-level hello execution plan that agrees with the import binding plan, concrete thread-context/user-stack/entrypoint mapping evidence, concrete exit/no-native-jump policy evidence, concrete x86_64 decoder and dispatch evidence, concrete milestone NT bridge checks, structured dispatch of `GetStdHandle`, `WriteFile`, and `ExitProcess`, an explicit fixture marker, and fixture execution through the CPU plan. The next required implementation phase is replacing the known-fixture bridge with broader x86_64 instruction decoding/dispatch, NT call bridging, and broader POSIX/thread/VM/container/renderer behavior for arbitrary PE programs.
