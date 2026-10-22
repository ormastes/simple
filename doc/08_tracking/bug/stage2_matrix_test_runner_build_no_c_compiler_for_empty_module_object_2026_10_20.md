# Stage 2 compiler-test matrix: test_runner_build fails with "no C compiler available for empty module object"

- Status: OPEN
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2 (blocks the full-CLI / Phase 4 matrix, not Stage 3)

## Observation

Full Stage 2 from release_phase3 f9527544c50 + the rt_process_rss_kib capsule
fix (bootstrap-r16b, Stage 2 sha256 645e62a815d0..., admitted). Its compiler
test matrix (`.simple/storage/build/bootstrap-r16b/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`) reports
`task=test_runner_build|result=FAIL|status=1|elapsed_seconds=299|max_rss_kib=7716648`;
`logs/test_runner_build.log` has 168 AOT errors of the form

```
error: AOT compile error -- unit, reason and lengths follow on the next lines
no C compiler available for empty module object build/native_cache/s4f880c5.../aot-<hash>.o.empty_module.c
```

The message comes from src/compiler/80.driver/driver_aot_native_output.spl:4245:
the empty-module object path needs a C compiler and finds none in the
matrix task's environment, although the same host builds C in Stage 1/2.

## Next step

Check how the matrix task builds its environment (PATH / CC under the
verification runner) against the empty-module object fallback's
compiler lookup.
