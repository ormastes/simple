<!-- codex-design -->

# System Test Plan: SimpleOS Wine Substrate

Date: 2026-05-06

## Gates

1. Capability matrix reports all Wine substrate rows and evidence paths.
2. Process-backed app QEMU lane has no resident fallback markers.
3. POSIX adapter tests cover fd, pipes, sockets, timers, errno, cwd/env/argv, and spawn.
4. Thread/TLS tests cover multiple threads, waits, timeouts, and per-thread fault attribution.
5. VM tests cover reserve, commit, protect, unmap, guard fault, execute permission, and fixed mapping conflict.
6. Container tests cover pid/fs/ipc/net namespace isolation.
7. Renderer/WM tests cover window lifecycle, damage/expose, input/focus, clipboard, text, and pixel parity.
8. PE parser tests cover valid console `hello.exe`, bad signature, wrong machine, unsupported subsystem, import summary, imported symbol extraction, relocations, TLS, entry-point mapping, image bounds, and bounds errors.
9. Modeled NT bridge tests cover the catalogued Win32/ntdll memory, file, thread/wait, process-env, heap, and Rtl calls while keeping them non-dispatchable for arbitrary PE imports.
10. Non-GUI `hello.exe` runs only after gates 1-9 plus minimal `KERNEL32.dll` import, image-layout, CPU, dispatch, and fixture-marker gates are verified.

## Evidence Commands

- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`
- `bin/simple test test/lib/common/wine_vm_adapter_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_posix_adapter_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_thread_adapter_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_dynload_adapter_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_service_adapter_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_precondition_manifest_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_precondition_fixture_builder_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_api_catalog_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_virtual_memory_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_file_io_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_thread_wait_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_process_env_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_nt_heap_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/wine_ntdll_bridge_spec.spl --mode=interpreter --clean`
- `bin/simple test test/lib/common/ui/wine_x11_adapter_spec.spl --mode=interpreter --clean`
- QEMU desktop process-backed app smoke command from existing SimpleOS desktop lane.
- Renderer golden/pixel parity harness from `src/app/wm_compare/`.
- PE fixture parser test once the parser module exists.
- `bin/simple run src/app/wine_hello/main.spl` for the known fixture command smoke once the milestone probe exists.

## Stop Condition

The Wine substrate milestone is not complete until every REQ row reaches `verified` and the known non-GUI `hello.exe` fixture either prints the expected output or fails with an expected structured unsupported-import, image-layout, CPU-execution, dispatch, or fixture-marker boundary error.
