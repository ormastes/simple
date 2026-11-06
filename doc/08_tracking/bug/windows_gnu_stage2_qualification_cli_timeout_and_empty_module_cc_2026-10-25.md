# Windows GNU Stage 2 qualification: full-CLI build timeout and empty-module C compiler ICE

Status: §1 FIXED 2026-11-06 (see "§1 fix" below); §2 OPEN. Found 2026-10-25 on DESKTOP-5A4V03J (Xeon W-2135, 32 GB), MinGW
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

## §1 fix 2026-11-06: direct COFF empty object, writer preferred over C discovery

Root cause: `driver_empty_object_supported` (`src/compiler/80.driver/driver_empty_object.spl`)
admitted only ELF targets, and `_compile_selected_module`
(`src/compiler/80.driver/driver_aot_native_output.spl`, empty-MIR branch) only
reached the direct writer after `find_c_compiler()` returned "" — and then keyed
it on `SIMPLE_NATIVE_BUILD_TARGET` alone, which is unset for host builds. On the
Windows GNU lane both conditions fail, so every empty module ICE'd.

Fix:
- `driver_empty_object_bytes(target, symbol)` now also emits a minimal COFF
  relocatable for `x86_64-*-windows*` (machine 0x8664) and `aarch64-*-windows*`
  (0xAA64): one 4-byte `.data` section and one `IMAGE_SYM_CLASS_EXTERNAL`
  symbol `simple_empty_module_<name>` (long name via string table) — the same
  shape `int <symbol> = 0;` compiles to. 110 bytes for a 23-char symbol.
- `driver_empty_object_target(explicit, host_os, host_arch)` falls back to the
  compiler host when no build target is set.
- The empty-MIR branch now tries the direct writer FIRST (ELF and COFF) and
  only falls back to the C stub + `find_c_compiler()` for unsupported targets
  (Mach-O).

Evidence (Windows host, llvm-mingw 20260922):
- `llvm-objdump -t -h` on the produced x86_64 object: `file format coff-x86-64`,
  `.data 00000004 DATA`, `[ 0](sec 1)(fl 0x00)(ty 0)(scl 2) (nx 0) 0x00000000
  simple_empty_module_a_b`; aarch64 object reads as `coff-arm64` with the same
  symbol.
- `clang -fuse-ld=lld main.o empty.o` with `main` reading
  `extern int simple_empty_module_a_b` links (rc=0) and runs (rc=0); the same
  link without the empty object fails with `ld.lld: error: undefined symbol`.
- `test/01_unit/compiler/80.driver/driver_empty_object_spec.spl`: 7/7 pass
  (3 new COFF/target `it`s), seed
  `simple-simdseed-20261106/.../bootstrap/simple.exe`.
- Not yet re-run: the Stage 2 `test_runner_build` matrix itself.
