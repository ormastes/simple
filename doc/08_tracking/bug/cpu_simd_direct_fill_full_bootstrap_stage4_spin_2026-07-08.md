# CPU SIMD Direct Fill Full Bootstrap Stage 4 Spin

Date: 2026-07-08

## Status

Open.

## Context

`rt_engine2d_simd_fill_u32` is registered in the Rust interpreter extern table
and the Simple SIMD fill path now calls it with scalar fallback. Retained
4K/8K performance evidence still needs a pure-Simple deployed binary before the
direct-fill path can be measured without using the Rust seed.

## Reproduction

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

Observed on `x86_64-unknown-linux-gnu`:

- Rust seed/runtime rebuild completed.
- Stage 2 produced `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`.
- Stage 3 reported no self-host executable and fell back to seed for stage 4.
- Stage 4 ran:
  `src/compiler_rust/target/bootstrap/simple run src/app/cli/native_build_main.spl -- --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 16 --cache-dir build/bootstrap/native_cache --mode dynload --entry src/app/cli/main.spl --runtime-path ... -o build/bootstrap/full/x86_64-unknown-linux-gnu/simple`
- The worker stayed CPU-bound for about 22 minutes before manual termination.
- `build/bootstrap/native_cache` contained only `bootstrap-wide-inputs.sha256`;
  no object output or full CLI executable was produced.

## Impact

The direct in-place SIMD fill path cannot yet be validated with retained
pure-Simple 4K/8K performance evidence from this workspace. Rust-seed tests can
prove the extern registration and source path, but retained performance reports
must wait for a successful pure-Simple deploy.

## Next Step

Investigate the stage-4 `--entry-closure` path before object output. Per the
unstable-build workflow, keep `build/bootstrap/native_cache` and use isolated
mini caches for smaller entries rather than clearing the main cache.
