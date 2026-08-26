# Native-build worker JIT prelude stalls before source closure

## Status

Open bootstrap blocker for the no-stub self-hosted CLI required by the headless
WM/GUI/Web/Engine2D Vulkan showcase.

## Reproduction

At source revision `98c9f01922c03582d3b0419d1d566b820d089c6a`, rebuild the
Rust seed, then run the cache-backed parse shard:

```sh
SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_NO_STUB_FALLBACK=1 \
src/compiler_rust/target/debug/simple run src/app/cli/native_build_worker.spl \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 8 \
  --cache-dir /mnt/data/worktrees/lane-amb3/build/bootstrap/native_cache \
  --mode dynload --entry src/app/cli/_CliMain/main_and_help.spl \
  -o build/native_probe/simple --parse-shard=0/8
```

The current seed includes the restored named-function closure boxing path, so
the prior `x64_lower_const` named-function JIT refusal no longer appears.
Instead, after the normal warning prelude it produces no `source_closure` line
or cache object for more than four minutes. At interruption, the worker had
five threads, was waiting at `futex_wait_queue`, used 2.59 GiB RSS (3.61 GiB
peak virtual memory), and the preserved cache still contained 893 files.

## Required follow-up

Add low-overhead JIT stage progress around module compilation and a bounded
worker receipt for this pre-source-closure wait. Diagnose the waiting worker
thread before changing renderer or QEMU evidence logic. No Vulkan showcase or
guest-frame claim may be admitted from a seed-only run.
