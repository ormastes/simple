# Compiler native linker still uses direct runtime imports

The LLVM native-link owner still imports `rt_env_get`, `rt_process_run`, and
file operations directly. The ARM64 freestanding dispatch added on 2026-07-12
keeps those calls inside that existing owner and adds no app/backend leakage.

TODO: migrate native linking to the canonical environment, process, and file
facades once those facades are available in the compiler bootstrap closure.
Keep the migration semantics-preserving and cover x86_64, ARM64, and RISC-V.

## Fixed (2026-07-17)

`src/compiler/70.backend/backend/llvm_native_link.spl` no longer declares its
own `extern fn rt_env_get`/`rt_process_run`/`rt_file_*`/`rt_dir_create_all`.
It now imports the canonical facade already used by the sibling
`llvm_backend_tools.spl` in the same directory:

```
use std.nogc_sync_mut.io_runtime.{env_get, file_delete, file_exists, file_write, process_run, dir_create_all}
```

All ~65 call sites across the hosted link path (entry-point/support C
compilation), the Stage4 symbol-closure scan, and the SimpleOS x86_64, ARM64,
and RISC-V (rv64/rv32) freestanding link routes were renamed to the facade
names (`env_get`, `process_run`, `file_exists`, `file_delete`, `file_write`,
`dir_create_all`). The previously-declared but never-called
`extern fn rt_file_write_bytes` was dead code and was deleted rather than
routed. No behavior change: `file_write` is the existing facade's wrapper
around the same `rt_file_write_text` primitive (plus an existing
missing-parent-directory retry already used by other callers of this facade
elsewhere in the compiler), and the other facade functions are 1:1 passthrough
wrappers over the same `rt_*` primitives previously called directly.

Verified: fresh trivial and `--emit-object` native-build probes succeed
(no seed-extern rejection), `sh scripts/check/native-smoke-matrix.shs` stays
green at `total=15 pass=15 fail=0 codegen_fallback_hits=0`, and
`sh scripts/audit/direct-env-runtime-guard.shs --working` reports
`STATUS: PASS` (that guard's scope is `src/app` + `src/lib/gc_async_mut`, so
this is not direct coverage of the compiler tree, but it is the mandated gate
and it stays green).
