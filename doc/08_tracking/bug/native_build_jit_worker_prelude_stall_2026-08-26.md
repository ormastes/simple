# Native-build worker JIT prelude stalls before source closure

## Status

Open bootstrap blocker for the no-stub self-hosted CLI required by the headless
WM/GUI/Web/Engine2D Vulkan showcase.

## Reproduction

At source revision `e35d34f9eed`, rebuild the Rust seed, then run the
cache-backed parse shard directly:

```sh
SIMPLE_EXECUTION_MODE=interpret SIMPLE_NATIVE_BUILD_WORKER=1 \
SIMPLE_NO_STUB_FALLBACK=1 \
src/compiler_rust/target/debug/simple run src/app/cli/parse_shard_main.spl \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 8 \
  --cache-dir /mnt/data/worktrees/lane-amb3/build/bootstrap/native_cache \
  --mode dynload --entry src/app/cli/_CliMain/main_and_help.spl \
  -o build/native_probe/simple --parse-shard=0/2
```

`run_parse_shards` previously launched `native_build_worker.spl`, contrary to
the slim entrypoint's contract. Revision `18c312d34d0` corrects that route.
The current seed includes the restored named-function closure boxing path, so
the prior `x64_lower_const` named-function JIT refusal no longer appears.
With `SIMPLE_JIT_STAGE_TRACE=1`, the old worker reaches:

```text
[jit-stage] compile_all:start functions=12611 globals=14814
```

before any `source_closure` line or cache object. A direct JIT diagnostic of
the corrected slim entry reaches a smaller, but still excessive, prelude:

```text
[jit-stage] compile_all:start functions=9819 globals=11339
```

Both JIT markers occur before source closure or cache progress. Production
children inherit `SIMPLE_EXECUTION_MODE=interpret` from the parent. Revision
`e35d34f9eed` caps that mode to two parse-shard processes by default (with the
measured-host override `SIMPLE_PARSE_SHARD_MAX`), avoiding the prior eight-way
11.6 GiB resident-heap burst. The capped production run reached the closure
walker, completed 1,809 discovery files, then advanced source closure to
704/1,047. It then made no further receipt for 83 seconds at about 1.79 GiB
RSS per child. The remaining blocker is a source-closure tail stall after
eager module loading, not merely JIT compilation or unsafe shard fan-out. The
preserved cache still contains 893 files.

## Required follow-up

Keep the two-process interpreter allocation cap. Then isolate and repair the
source-closure tail immediately after
`src/lib/nogc_sync_mut/tooling/easy_fix/accessor_core.spl` (the 704 receipt),
with a bounded per-file receipt rather than another whole-worker retry.
Splitting only the full CLI removes 2,792 JIT functions but is insufficient.
No Vulkan showcase or guest-frame claim may be admitted from a seed-only run.
