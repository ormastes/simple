# Compiler native linker still uses direct runtime imports

The LLVM native-link owner still imports `rt_env_get`, `rt_process_run`, and
file operations directly. The ARM64 freestanding dispatch added on 2026-07-12
keeps those calls inside that existing owner and adds no app/backend leakage.

TODO: migrate native linking to the canonical environment, process, and file
facades once those facades are available in the compiler bootstrap closure.
Keep the migration semantics-preserving and cover x86_64, ARM64, and RISC-V.
