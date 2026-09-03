# Boot autodiscovery compiles `.inc.c` include-fragments as standalone TUs

**Filed** 2026-09-01 · **Status** OPEN · **Severity** medium

## Symptom
Every riscv64 WM kernel build reports:

    WARNING: 5 boot source file(s) failed to compile; resulting ELF may have undefined refs

The five are `baremetal_runtime_services.inc.c`, `baremetal_runtime_network_tail.inc.c`,
`rv64_fs_exec_media.inc.c`, `rv64_fs_exec_loader.inc.c` and
`full_networking_runtime.c`, failing with `use of undeclared identifier` on
things like `g_riscv_process_arena`, `g_rv_vnet`, `uint32_t`.

## Root cause
`native_project/linker.rs:2130` selects boot sources with
`path.extension() == Some("c")`. A file named `foo.inc.c` **has** extension `c`,
so include-fragments -- which are meant to be textually included into a host TU
and are not self-contained -- are compiled standalone and necessarily fail.

## Why it matters
The failure is a WARNING, so it is indistinguishable from a real breakage and
trains readers to ignore the line. During the 2026-09-01 rv64 WM link
investigation these five failures were the first hypothesis for 66 undefined
symbols and cost a full diagnostic cycle to rule out (measured: **0** of the 66
were defined in any of the five).

## Fix sketch
Skip stems ending in `.inc` during boot autodiscovery, and make a genuine `.c`
TU that fails to compile a hard ERROR rather than a warning -- the current
policy is what let `freestanding_runtime.c` sit uncompilable indefinitely (see
`rv64_src_boot_freestanding_runtime_never_compiles_2026-09-01.md`).
