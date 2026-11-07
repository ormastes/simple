# Bootstrap Progress (release/1.0.0, macOS arm64)

Living status of the bootstrap stages. One row per stage; update the row in place.

| Stage | Status | Blocker / root cause | PR |
|-------|--------|----------------------|----|
| Stage 2 | fix landed, rerun pending | `test_runner_build` PASS. `compiler_cli_build` timed out at 14400 s with 24/3095 modules staged (8-module codegen batches took 1688 s, 1144 s and 5210 s). Profiling (`sample`, test_runner build, serial codegen lane): 43% of main-thread samples were in `reverse_reference_sorted_v1` and ~0.5% in LLVM `compile_ir_to_object_path`. Every `build_cache.save()` (once per module at `driver_aot_native_output.spl:1303`, once per batch at `:2901`) rebuilt, sorted and published the whole-program reverse-reference receipt, so cost grew as modules x facts log facts. Fix: intermediate saves write entries only (`save_entries`); the final save publishes the receipt (readers already fail closed on a stale generation). | #7649 |
