# Self-hosted child test binary erases class values across module boundaries

> **Same defect as [`class_field_access_erased_under_test_runner_2026-08-18.md`](class_field_access_erased_under_test_runner_2026-08-18.md)**,
> filed independently the same day by another lane agent. Scope correction:
> the cross-module framing in THIS record is too narrow — a self-contained
> spec with a purely local class fails identically, so a module boundary is
> not required to trigger it. What this record adds and the other does not is
> that METHOD dispatch is erased too, not only field access.


**Date:** 2026-08-18
**Status:** OPEN
**Severity:** HIGH (blocks any spec that drives a class instance defined in another module)
**Child binary:** `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple` (as reported by the test runner's `child binary:` line)

## Symptom

Under `bin/simple test`, a class value that crosses a module boundary — as a
return value, a parameter, or even a value constructed inside the callee's own
module after the call chain entered through a cross-module `pub fn` — degrades
to type `object`:

- `semantic: method 'update_entry' not found on type 'object' (receiver value: BuildCache(...))`
- `semantic: undefined field 'cache_path': cannot access field on value of type 'object'`
- `semantic: method 'freeze_storage_registry' not found on type 'object' (receiver value: CompileContext(...))`

The printed receiver value shows the correct class and fields — only the
static identity is lost.

## Evidence it is pre-existing (not introduced by the Phase D cache work)

`test/01_unit/compiler/driver/native_capsule_result_receipt_spec.spl` at
clean HEAD (my working-tree edits reverted via `git checkout HEAD -- <paths>`)
already fails identically:

```
semantic: method `freeze_storage_registry` not found on type `object` (receiver value: CompileContext(...))
Results: 2 total, 0 passed, 2 failed
```

Three escalating attempts while writing
`test/01_unit/compiler/driver/dep_interface_cache_key_spec.spl` narrowed the
shape:
1. direct method calls from the spec — method not found on `object`;
2. in-module free functions taking `cache: BuildCache` — method still not
   found inside the callee;
3. path-based entry points where the instance never leaves
   `driver_build/incremental.spl` (`BuildCache.load` called inside the module)
   — even plain FIELD access (`cache.cache_path`) fails once the call chain
   entered through a cross-module `pub fn`.

Static fns and free functions over plain data (text, [text], bool, Option)
work throughout.

## Impact

- `native_capsule_result_receipt_spec.spl`: RED at HEAD (0/2).
- The Phase D interface-digest gate cannot be spec'd end-to-end through a
  BuildCache instance; the spec instead exercises the gate's plain-data pair
  `dep_iface_gate_record` / `dep_iface_gate_valid` — the exact functions the
  BuildCache record/validate paths call.

## Unblock condition

A redeployed self-hosted child binary that preserves class identity across
module boundaries; then fold the BuildCache round-trip cases (persist +
reload + sabotage of the persisted `deps_iface` row) back into
`dep_interface_cache_key_spec.spl`.
