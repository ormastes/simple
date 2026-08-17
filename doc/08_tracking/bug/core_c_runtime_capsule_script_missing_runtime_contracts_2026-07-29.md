# `build-core-c-bootstrap-runtime-capsule.shs` fails: `simple_contract_check` provider moved

- **Filed:** 2026-07-29
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Script:** `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`
- **Severity:** blocks the C-capsule lane for rebuilding `libsimple_runtime.a`

## Symptom

The script fails with `archive-simple_contract_check-provider-missing`.

## Cause

`simple_contract_check` moved to `src/runtime/runtime_contracts.c`, which the
script neither compiles nor accepts as a provider. The script's source list is
stale relative to the runtime tree.

## Why it matters

Found while recovering the stage-4 bootstrap from a stale-runtime link failure
(undefined `rt_transient_heap_promote` / `rt_file_is_regular_no_follow`: every
prebuilt `libsimple_runtime.a` on the host was missing symbols that
`src/runtime/runtime_native.c` defines). The C-capsule script is one of the two
lanes for rebuilding that archive; with it broken, only the cargo lane works:

```
cargo build --profile bootstrap -p simple-runtime   # inside the (work)tree
nm target/bootstrap/libsimple_runtime.a | grep -c 'rt_transient_heap_promote\|rt_file_is_regular_no_follow'  # must be >= 2
```

A stale archive fails at STAGE-3 LINK time with plain `undefined reference`
errors — nothing names the archive as the culprit, so it reads like a compiler
bug. Check the archive with `nm` before suspecting codegen.

## Fix

Add `runtime_contracts.c` (and audit for other moved providers) to the capsule
script's compile list, then prove the gate both ways: capsule build succeeds
from a clean tree, and deleting a provider makes it fail naming that provider.
