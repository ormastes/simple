# `std.collection_helpers` module does not exist — spec covers 33+ unimplemented functions

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/common/collection_helpers_spec.spl`, 0/1 examples
  executed — reported as "1 total, 0 passed, 1 failed" because the whole
  file fails to compile, but the spec declares 70+ examples per the runner's
  own `declared>=70` verdict field).

## Symptom

```
use std.collection_helpers.*
```

```
error: semantic: Cannot resolve module: std.collection_helpers
error: test-runner: no examples executed
```

`test/01_unit/lib/std/common/collection_helpers_spec.spl:28` imports
`std.collection_helpers`, and its header (`# @cover
src/lib/common/collection_helpers.spl 80%`) names the expected implementation
file. Neither the module nor the file exists anywhere in the tree:

```bash
find src/lib -iname "collection_helpers*"   # no output
grep -rln "fn sort_by_key" src/lib/          # no output
grep -rln "fn min_by_key" src/lib/           # no output
```

## Scope

The spec (per its own docstring) covers `sort_by_key`, `min_by_key`,
`max_by_key`, `flat_map`, `compact_map`, `insert_at`, `remove_at`, `arr_pop`,
`arr_shift`, `reject`, `none`, `one`, `find_last`, `find_last_index`, `at`,
`arr_clone`, `each_slice`, `chunk`, `pairwise`, `sum_by`, `product`, `tally`,
`compress`, and more — none of these exist in `src/lib` under any name
searched. This is not a broken test or an import-path typo; it is an entire
unimplemented stdlib module ("Phase 1 collection helper functions" per the
spec's overview), which is substantial net-new feature work, not a safe
mechanical fix.

## Why not fixed here

Implementing 20+ new stdlib functions correctly (including edge-case
semantics like `each_slice`/`chunk`/`pairwise`/`tally`/`compress`) is a
feature-scope task, explicitly out of scope for a triage/fix pass that is
supposed to avoid risky, large changes without dedicated review.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/common/collection_helpers_spec.spl
```
