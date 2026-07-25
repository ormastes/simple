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

On 2026-07-25, after the CLI global-flag parser split (`4392ce6...`) and
repo-local seed fallback (`debc189...`), a clean workspace
`/home/ormastes/dev/pub/simple-redeploy-clean` reproduced the same pre-object
state:

- Main CLI probe:
  `SIMPLE_NO_STUB_FALLBACK=1 /home/ormastes/dev/pub/simple/bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 8 --cache-dir build/bootstrap/native_cache --mode dynload --entry src/app/cli/_CliMain/main_and_help.spl -o build/native_probe/simple`
  hit a 240s cap with zero log lines and zero cached `.o` files.
- Bootstrap shard:
  `SIMPLE_NO_STUB_FALLBACK=1 /home/ormastes/dev/pub/simple/bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 4 --cache-dir build/mini_cache_bootstrap_main --mode dynload --entry src/app/cli/bootstrap_main.spl -o build/mini_builds/bootstrap_main/simple_bootstrap`
  hit a 180s cap with zero log lines and zero cached `.o` files.

No child process from those clean-workspace probes remained afterward. An
unrelated MCP mini build was active in `/home/ormastes/dev/pub/simple` and was
left untouched.

## Expected

The shard should either emit cached objects/its executable or fail with a
specific diagnostic within the bootstrap verification window.

## Follow-up

Profile the entry-closure/HIR-to-MIR phase before object emission and add a
phase-progress timeout diagnostic. Reuse the command above with its isolated
cache; do not disable `SIMPLE_NO_STUB_FALLBACK`.
