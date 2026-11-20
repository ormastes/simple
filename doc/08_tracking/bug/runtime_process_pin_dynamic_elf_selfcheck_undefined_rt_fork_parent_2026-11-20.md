# Linux owned-pin selfcheck fails to link: undefined `rt_fork_parent_*_cpu_micros`
- Status: open
- Severity: P3
- Found: 2026-11-20, ubuntu-p2 WSL2 (clang, origin/release/1.0.0 `82087d024a1`)
- Component: C runtime selfchecks (`src/runtime/test/`), `src/runtime/runtime_fork.c`

## Observation
Following the file's own header recipe, the Linux dynamic-ELF pin selfcheck no longer links.
`clang -std=gnu11 -O0 -pthread src/runtime/test/runtime_process_pin_dynamic_elf_linux_selfcheck.c -o /tmp/x`
-> `undefined reference to rt_fork_parent_user_cpu_micros` and `rt_fork_parent_system_cpu_micros`; linker exits 1.

## Evidence
- The selfcheck `#include`s `../runtime_process.c` and `../runtime_process_owned.c` (selfcheck:98-99) but not `runtime_fork.c`.
- `runtime_process.c:2640,2648,2649` now calls `rt_fork_parent_peak_rss_bytes()`, `rt_fork_parent_user_cpu_micros()`, `rt_fork_parent_system_cpu_micros()`.
- Definitions: POSIX in `runtime_fork_capture_context_private.h:98` (pulled in by `runtime_fork.c`'s POSIX branch, :74+); only Windows stubs at `runtime_fork.c:50-52`. No Rust-runtime definition.
- Sibling `runtime_process_owned_pinned_integration_selfcheck.c` also fails with plain `clang` (undefined `rt_process_pin_*`); it presumably needs extra sources, not checked further.

## Needed
Add the `runtime_fork.c` dependency (include it or link stubs) to the selfcheck and update its header recipe; consider a CI gate that compiles+links each selfcheck.
