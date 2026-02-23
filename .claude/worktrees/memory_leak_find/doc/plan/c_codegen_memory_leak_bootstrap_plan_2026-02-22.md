# C Codegen Memory-Leak Bootstrap Plan (2026-02-22)

## Goal
Stabilize C backend bootstrap by removing memory-leak-prone codegen patterns while keeping LLVM-shared interface behavior and clang/clang-cl + CMake compatibility.

## Scope
- `src/compiler/70.backend/backend/*`
- `src/compiler/backend/backend/*` (synced tree)

## Plan And Status
1. Audit C codegen allocation semantics vs MIR/LLVM semantics
- Status: completed
- Result: MIR `Alloc` was heap-emitted via `spl_malloc`, unlike LLVM `alloca` semantics.

2. Remove leak-prone heap emissions in C backend
- Status: completed
- Result:
  - Replaced `Alloc`/`Aggregate`/`GpuSharedAlloc` heap emission with reusable function-local stack slots.
  - Added pre-scan (`prepare_stack_slots`) + slot sizing/assignment helpers.

3. Fix composite constant allocation behavior
- Status: completed
- Result:
  - Added composite-const lowering that initializes stack slots when a destination local exists.
  - Replaced heap-based const composite expressions with static literal expressions.

4. Keep clang/clang-cl compatibility in generated `.h/.cpp`
- Status: completed
- Result: clang-cl macro path and unreachable macro handling are present in both backend trees.

5. Enforce CMake generation policy
- Status: completed
- Result: both backend trees now generate per-dir `CMakeLists.txt` and `generated_sources.cmake`, without generating root `CMakeLists.txt`.

6. Verify generated C++ compileability
- Status: partial
- Result:
  - `clang++` syntax smoke test passed for newly generated stack-slot/static-const patterns.
  - End-to-end `simple compile --backend=c` currently blocked by existing workspace/runtime errors (`get_cli_args` missing and module export resolution warnings/errors in interpreter path).

7. Remove remaining helper-runtime leak paths used by C codegen
- Status: completed
- Result:
  - Patched dict helper runtime in `src/app/compile/c_runtime.c` and `src/compiler_cpp/c_runtime.c`:
    - free old string payload when overwriting dict entry kind (`set_int`, `set_ptr`, `set_str`)
    - free removed key/value in `simple_dict_remove`
    - avoid per-call heap allocation in int `simple_dict_get` conversion (static buffer)
  - These changes remove persistent heap growth from repeated dictionary updates/removals in generated C/C++ helper paths.

8. Remove per-call string allocations in Option/Result helper constructors
- Status: completed
- Result:
  - Updated runtime helper constructors in `src/app/compile/c_runtime.c` and generated compiler C files (`src/compiler_cpp/*.c`):
    - `simple_some_str`: no longer `strdup` per constructor call
    - `simple_result_ok_str`: no longer `strdup` per constructor call
    - `simple_result_err_str`: no longer `strdup` per constructor call
  - Updated `simple_int_to_str` in the same files to use static buffer return, removing per-call heap allocation.
  - This removes high-frequency transient allocations from core Option/Result/string-conversion helper paths during long compiler runs.

## Next Bootstrap Step
- Current state (updated):
  - `bin/simple compile --backend=c ...` no longer hangs; it now succeeds via bootstrap fallback generator (`bin/bootstrap/cpp/simple gen-c`) and emits C output.
  - Native handler path (`rt_cli_handle_compile`) still fails with non-zero in this build, so bootstrap fallback remains the active path unless native is repaired.
  - Build hint for fallback output is now clang-based (`clang -std=gnu11 -O2 ... -lm`).
  - Module-path repair in block re-exports removed `compiler_shared.blocks.*` resolution failures and now routes through concrete `compiler.blocks.blocks.*`.
- Remaining blocker:
  - Bootstrap-generated C can still fail strict compile checks when unresolved-import stubs drift from real function signatures; one concrete case (`run_leak_check` arity mismatch) was fixed by normalizing leak-check entry signature to `run_leak_check()`.
- Next work:
  - Keep bootstrap fallback as stable generation path for now.
  - Repair native compile handler implementation availability in runtime build.
  - Improve bootstrap generator fidelity for unresolved import stubs, then rerun end-to-end compileability checks (`clang`/`clang++`, and `clang-cl` where available) and capture results in bug report.
  - Continue sweeping larger CLI subcommands one-by-one under `--backend=c` to identify remaining stub/signature mismatches early.
