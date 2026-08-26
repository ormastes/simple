# Native-build worker JIT prelude stalls before source closure

## Status

Open bootstrap blocker for the no-stub self-hosted CLI required by the headless
WM/GUI/Web/Engine2D Vulkan showcase.

## Reproduction

At source revision `18c312d34d0`, rebuild the Rust seed, then run the
cache-backed parse shard directly:

```sh
SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_NO_STUB_FALLBACK=1 \
src/compiler_rust/target/debug/simple run src/app/cli/parse_shard_main.spl \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 8 \
  --cache-dir /mnt/data/worktrees/lane-amb3/build/bootstrap/native_cache \
  --mode dynload --entry src/app/cli/_CliMain/main_and_help.spl \
  -o build/native_probe/simple --parse-shard=0/8
```

`run_parse_shards` previously launched `native_build_worker.spl`, contrary to
the slim entrypoint's contract. Revision `18c312d34d0` corrects that route.
The current seed includes the restored named-function closure boxing path, so
the prior `x64_lower_const` named-function JIT refusal no longer appears.
With `SIMPLE_JIT_STAGE_TRACE=1`, the old worker reaches:

```text
[jit-stage] compile_all:start functions=12611 globals=14814
```

before any `source_closure` line or cache object. The corrected slim entry
reaches a smaller, but still excessive, prelude:

```text
[jit-stage] compile_all:start functions=9819 globals=11339
```

Both markers occur before source closure or cache progress. At interruption,
the old worker had five threads, was waiting at `futex_wait_queue`, used 2.59
GiB RSS (3.61 GiB peak virtual memory), and the preserved cache still contained
893 files. The slim probe was stopped at 1.81 GiB RSS after its marker.

## Required follow-up

Keep the stage markers and route parse-shard closure planning through an entry
that does not JIT any complete compiler prelude; splitting only the full CLI
removes 2,792 functions but is insufficient. Add a bounded worker receipt for
this pre-source-closure wait. No Vulkan showcase or guest-frame claim may be
admitted from a seed-only run.
