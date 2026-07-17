# macOS bootstrap Rust-hosted archive lacks `copy_mem`

## Status

Open. The third and final bounded bootstrap cycle reached the Stage 3 linker
and failed on one undefined symbol.

## Evidence

The corrected `main` sources were compiled with the fresh Stage 3 compiler and
the isolated cache under `build/native_probe/main_closure/cache-stage3`.
`build/native_probe/main_closure/logs/stage3-fixed2.log` ends with:

```text
Undefined symbols for architecture arm64:
  "_copy_mem", referenced from:
      _compiler_rust__lib__std__src__core__list__List_dot_reserve
```

`copy_mem` is implemented by the monolithic `runtime_native.c` and pure-Simple
`simple_core/core_memory.spl`, but the Rust-hosted archive currently exports
only `rt_memcpy` from `runtime_memory.c`. The failure is therefore provider
composition, not source lowering.

## Required fix

Give the Rust-hosted memory component an ABI-compatible `copy_mem` owner that
forwards to `rt_memcpy`, add a discriminating overlap/copy regression, rebuild
`simple-native-all`, and rerun only the cached Stage 3 shard in a fresh turn.
The core-C Stage 4 profile must continue rejecting duplicate providers.
