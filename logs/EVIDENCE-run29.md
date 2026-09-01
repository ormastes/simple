# run29 rebuild evidence (2026-08-23)

Worktree /mnt/data/worktrees/redeploy-1 @ 619a9a616ad (origin/main).
All 7 target fixes verified as ancestors (619a9a616ad D4, 7127df8d794 D2,
63f4b5d1362 D1, 9c5e2dad378, c249680becc, 8e9fd4efeb2, ee40943016a).

## Stage 2 (PASS)
749 compiled, 0 cached, 0 failed. 619.0s compile + 95.5s link = 714.5s.
Binary 129820 KB, linked via clang++. "Stage 2 admitted; stopping before Stage 3."
Log: build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log

Deviation from brief: brief's exact command exits 64
("bootstrap-policy-error: reason-receipt-required"); --stop-after-stage2 added,
it is the sole receipt-free lane per the script's own --help.
Seed downgrades --mode=dynload to one-binary (E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED).

## Hello world (FAIL, rc=139, deterministic 4/4)
Source (verbatim, 2 lines):
    fn main():
        print("hello world")

Stock settings, `native-build`: rc=139 SIGSEGV, no output binary. Reproduced 4/4.

Backtrace A (stock, crash at step 2/6):
 #0 compiler.hir.generated.hir_codec.hc_enc_hir_type
 #1 hc_enc_hir_symbol
 #2 hc_enc_symbol_table
 #3 hc_enc_hir_module
 #4 compiler.hir.hir_codec.hir_module_encode
 #5 compiler.driver.driver_hir_cache.hir_cache_store
 #6 driver_hir_pipeline_lowering.CompilerDriver.lower_and_check_impl
 #7 driver_orchestration.CompilerDriver.compile
 #8 app.cli.bootstrap_main.run_native_build_bootstrap

Backtrace B (SIMPLE_HIR_CACHE=0, diagnostic only; gets to step 5/6 then rc=139):
 #0 driver_aot_native_output._compile_frozen_module_capsule
 #1 driver_aot_native_output.CompilerDriver.compile_to_native
 #2 app.cli.bootstrap_main.run_native_build_bootstrap

=> TWO distinct SEGVs, serially blocking. A is in the HIR cache ENCODE path
(D1 fixed the DECODE side); B is in AOT native capsule compile, previously
masked by A.

`compile` subcommand: rc=1, "error: bootstrap compile supports --format=smf only"
(not a crash; wrong-format rejection).

## Steps 3-5: BLOCKED, not attempted.
Stage 3, tool builds and the 2,179-spec sweep all drive this same binary through
native-build; every one would return rc=139.
