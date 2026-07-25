# Bootstrap `bootstrap_main` native build makes no object progress

## Observed

On 2026-07-23, the bootstrap-only Rust seed ran this no-stub shard for more
than 15 minutes at about one CPU and 1.5 GiB RSS without producing an object:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --backend cranelift \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --threads 8 --cache-dir build/mini_cache_bootstrap_flat_globals \
  --mode dynload --entry src/app/cli/bootstrap_main.spl \
  -o build/native_probe/simple_bootstrap_flat_globals
```

The log stopped changing after import/GC warnings. The process remained
CPU-active with a defunct child and zero cached `.o` files, so the repo runaway
guard required termination. Temporary log and empty cache were removed.

## Expected

The shard should either emit cached objects/its executable or fail with a
specific diagnostic within the bootstrap verification window.

## Follow-up

Profile the entry-closure/HIR-to-MIR phase before object emission and add a
phase-progress timeout diagnostic. Reuse the command above with its isolated
cache; do not disable `SIMPLE_NO_STUB_FALLBACK`.
