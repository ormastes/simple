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
8. PE parser tests cover valid console `hello.exe`, bad signature, wrong machine, unsupported subsystem, import summary, relocations, TLS, and bounds errors.
9. Non-GUI `hello.exe` runs only after gates 1-8 are verified.

## Evidence Commands

- `bin/simple test doc/06_spec/app/simpleos/feature/simpleos_wine_substrate_spec.spl`
- QEMU desktop process-backed app smoke command from existing SimpleOS desktop lane.
- Renderer golden/pixel parity harness from `src/app/wm_compare/`.
- PE fixture parser test once the parser module exists.

## Stop Condition

The Wine substrate milestone is not complete until every REQ row reaches `verified` and the non-GUI `hello.exe` fixture either prints the expected output or fails with an expected structured unsupported-import error.

