# Native entry closure requires unavailable `rt_env_vars`

Date: 2026-09-09  
Status: open; blocks compiled Slang owner-fixture qualification.

## Reproducer

```text
simple native-build --backend=cranelift \
  --source test/fixtures/slang_paged_kv_provider --source src/lib \
  --entry-closure \
  --entry test/fixtures/slang_paged_kv_provider/owner_smoke.spl \
  --output /tmp/slang-owner-smoke-native
```

The fixture uses only the direct `rt_cli_get_args` intrinsic plus Slang modules,
but entry-closure compilation ends with:

```text
error: semantic: unknown extern function: rt_env_vars
```

## Required acceptance

- Report the exact dependency path that admits `rt_env_vars` into the closure.
- Either link its canonical runtime implementation or exclude the unrelated
  environment module from the closure.
- Build and run the real Slang owner fixture without adding a fake extern or
  broadening its runtime authority.
