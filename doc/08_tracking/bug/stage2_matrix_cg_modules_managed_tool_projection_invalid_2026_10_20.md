# Stage 2 compiler-test matrix: src/app/_cg modules fail with "managed tool projection role/path/digest invalid"

- Status: OPEN
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2 (blocks the full-CLI / Phase 4 matrix, not Stage 3)

## Observation

Same run as `stage2_matrix_test_runner_build_no_c_compiler_for_empty_module_object_2026_10_20.md`. The matrix's module compile campaign fails 7 entries
(`module_compile_retained_failures|result=FAIL|status=sealed-failures|count=7`):
src/app/_cg/f06, f07, f08, f08b, f08c, f08v and p3 `main.spl`, each in
15-22 s, with

```
error: managed tool projection role/path/digest invalid
```

(`module-diagnostics/attempt.*/N/compile.log`). The text is returned by
src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl:93, so the managed
native-tool projection the Stage 2 compiler is handed in the matrix does
not validate.
