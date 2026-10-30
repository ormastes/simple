# Windows GNU Stage 2 qualification: full-CLI build timeout and empty-module C compiler ICE

Status: OPEN. Found 2026-10-25 on DESKTOP-5A4V03J (Xeon W-2135, 32 GB), MinGW
clang default lane (llvm-mingw 20260922, Rust host `x86_64-pc-windows-gnullvm`,
`--backend=cranelift`), `origin/release/1.0.0` @ `a853ac75861` plus
`a3f9a50d853` (sffi time fix).

## What passed

`bootstrap-windows.sh --full-bootstrap --stop-after-stage2 --mode=dynload
--jobs=half --backend=cranelift` produced and admitted Stage 2
(`d14badc8e34d536a3b6b1466340d391478048ade04b5eb070811eb2e4c43bab9`,
`simple-bootstrap 1.0.0-rc.1`): link through llvm-mingw `ld.lld` + libunwind,
frontend sanity (p2_add, hello-world-positional, MIR retention, module path
naming) all PASS. Incremental cache: 1525 reused / 21 rebuilt.

## What failed (phase verification matrix, `overall=FAIL`)

Summary: `.simple/storage/build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-gnu/verification/summary.env`.

| task | result | detail |
|---|---|---|
| compiler_version | PASS | 3 s |
| compiler_cli_build | CRASH 134 | killed at 1838 s by `native_internal_timeout_seconds=1800`; HIR had reached 100/2937 modules (~17.8 s/module). `native-build worker wrapper exited abnormally (code -1)` |
| test_runner_build | FAIL 1 | 64 caught codegen ICEs, all `no C compiler available for empty module object build/aot-*.o.empty_module.c` |
| compiler_bootstrap / interpreter / loader tests | UNSUPPORTED | `full-cli-artifact-not-built` |

### 1. Empty-module object path cannot find clang

`_compile_selected_module` (`src/compiler/80.driver/driver_aot_native_output.spl:4278`)
emits an empty translation unit for function-less modules and compiles it with
`find_c_compiler()` (`src/compiler/70.backend/backend/runtime_compiler.spl:253`).
The other modules of the same build compiled their C through the lane's bound
C tool (`target_c_tool_path=.../llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe`),
so the lane has a working clang. The empty-module path uses separate PATH discovery
(`_find_c_compiler_windows` → `_first_verified_windows_compiler("clang")`). That
discovery does not honour the lane's binding, and it returns "" under the matrix
environment. Expected: the empty-module compile must use the same admitted C tool
as every other object of the build, not a second discovery.

### 2. Full CLI build is ~18 s per HIR module on this host

At that rate 2937 modules need ~14 h; the 1800 s internal timeout kills it.
The HIR cache was cold (`[hir-cache-store] refused reason=decode` for
`src/app/cli/_CliMain/main_and_help.spl`). Not yet profiled; record measured
rate with the binary identity above before changing the timeout.

## Impact

Stage 2 is usable as an explicitly-admitted compiler for focused native builds
(`native-build --runtime-bundle core-c-bootstrap --entry-closure`), which is how
the SIMD DB/web probes are built. It is not a qualified phase: no full CLI, no
test runner, and Stage 3/4 remain blocked on this host.
