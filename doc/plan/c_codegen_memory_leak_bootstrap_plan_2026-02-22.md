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

## Next Bootstrap Step
- Unblock `simple compile --backend=c` execution path, then run full generated-output compile checks (`clang++` and `clang-cl` where available) and capture results in bug report.
