# C Codegen Bootstrap Alignment Plan (2026-02-22)

## Scope

Align C/C++ bootstrap codegen with the shared backend interface expectations and bootstrap output requirements:

1. Verify C codegen interface parity with LLVM/Cranelift adapters.
2. Ensure generated `.h`/`.cpp` are clang/clang-cl friendly (including Windows clang-cl conditionals).
3. Generate `CMakeLists.txt` per generated directory, but do not generate root `CMakeLists.txt` (root should include generated cmake fragment).
4. Remove known static compile blockers in generated C++ output path before runtime compile verification.
5. Update C codegen pipeline files accordingly and capture findings in a bug report text file.

## Current Status (Review Snapshot)

- `CCodegenAdapter` implements the shared `Codegen` trait methods (`backend_kind`, `backend_name`, `supports_target`, `output_kind`, `compile_module`).
- `CraneliftCodegenAdapter` currently returns a compiled-mode error stub; this is not a C backend bug but is relevant to interface parity expectations.
- C backend multi-file output currently emits both `generated_sources.cmake` and a root `CMakeLists.txt` (violates requirement #3).
- C IR builder emits portability conditionals, but clang-cl-specific detection is implicit and not explicit.
- Static generated-C++ risk found: arithmetic/unary/compare helper emission redeclares locals that are already declared in function prologue; this can produce C++ compile failures.
- Static generated-C++ risk found: load translation redeclares destination local instead of assigning to existing local.

## Implementation Plan

1. Harden C++ emission semantics.
   - Update C IR builder emit helpers to assign to existing locals instead of redeclaring temporaries for binop/unary/cmp.
   - Fix MIR load translation in C backend to assignment form.

2. Improve clang-cl compatibility markers in generated code.
   - Add explicit clang-cl detection macro in generated `.h`/`.cpp`.
   - Keep portable `SPL_UNREACHABLE()` mapping with Windows/MSVC/clang-cl branches.

3. Fix CMake generation policy for directory output.
   - Keep per-directory `CMakeLists.txt`.
   - Keep root `generated_sources.cmake`.
   - Stop generating root `CMakeLists.txt`.
   - Adjust generated fragment comments/variables for inclusion by project root CMake.

4. Record review findings and fixes in bug report text.
   - Add/update bug report text under `doc/bug/` with concrete issues and fix status.

5. Defer compile validation.
   - Do not run compile/build commands until explicitly approved.

## Exit Criteria For This Pass

- Plan doc committed in tree.
- C codegen files updated for static correctness and policy compliance.
- Bug report text updated with fixed findings and pending compile validation note.
- No compile invocation performed in this pass.
