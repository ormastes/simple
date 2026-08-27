# Native entry closure excludes executable `src/app/doc` modules

- Status: fixed in source; self-hosted native-build confirmation pending.
- Owner: compiler driver source loading.
- Area: `src/compiler/80.driver/driver_source_loading.spl`.

## Reproduction

An entry-closure build rooted at `src/app/cli/main.spl` resolves
`app.doc.public_check.statistics` to
`src/app/doc/public_check/statistics.spl`, then reports that the resolved
module is empty or excluded.

## Root cause

`_driver_collect_entry_import_source` excluded every path containing `/doc/`.
That policy is correct for documentation fixtures but also matched executable
application modules stored under `src/app/doc/`.

## Repair and regression

The collector now exempts only normalized `src/app/doc/` paths from that one
documentation exclusion; test, testdata, verification, and other documentation
filters remain unchanged. The direct regression is
`test/01_unit/compiler/driver/driver_source_loading_spec.spl`, which verifies
that the collected source retains module identity
`app.doc.public_check.statistics`.

## Remaining qualification

The post-fix native build passed the former excluded-module point but remained
CPU-bound in the broader self-hosted entry-closure compilation and was stopped
under the bounded-build guard. Resume with one cache-preserving build only after
an admitted Stage-4 driver is available:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry src/app/cli/main.spl --entry-closure --threads 8 \
  --cache-dir build/bootstrap/native_cache --mode dynload \
  --output build/mini_builds/v9_selfhosted/simple
```
