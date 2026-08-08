# `core_intensive_spec.spl` is VACUOUS — it tests local stub classes, not `std.database.core`

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --timeout 800 test/02_integration/compiler
#   FAIL test/02_integration/compiler/core_intensive_spec.spl (21 passed, 11 failed)
#   Error: semantic: method `has_column` not found on type `SdnRow`
```

`has_column` **does** exist on the real `SdnRow`
(`src/lib/nogc_sync_mut/database/core.spl:189`), so the error looks like a
compiler symbol-resolution defect. It is not.

## Root cause (proven)

`test/02_integration/compiler/core_intensive_spec.spl:5-6` — the imports of the
subject under test are **commented out**:

```simple
# use std.database.core.{StringInterner, SdnTable, SdnRow, SdnDatabase}
# use test.lib.database_fixtures.{generate_simple_string, ...}
```

and replaced, in the same file, by hand-written copies:

```
:16   # Stub: StringInterner
:17   class StringInterner:
:39   # Stub: SdnRow
:40   class SdnRow:
```

The file has **no `use` statements at all** (`grep -n '^use ' …` returns
nothing). Every one of its 32 examples binds `SdnRow`/`SdnTable`/
`StringInterner` to the local stubs. The stub `SdnRow` is a `class` with a
single `fields` member and no `has_column` method; the real one is a `struct`
with `fields` + `_version` and does have `has_column`
(`core.spl:122`, `:189`).

So:

* The 11 failures are failures of the **stub**, not of the product.
* The 21 passes prove nothing about `std.database.core` — they are a local
  class exercising itself.
* A total regression of `std.database.core` would leave this spec green.

Same shape as the previously-recorded shim-vacuity findings. Note also that the
file lives under `test/02_integration/**compiler**/` while its declared subject
is the database library — it is misfiled as well as vacuous.

## Why not fixed now

Restoring the real imports is the correct fix, but it is not a one-line change:
the stubs diverged from the real API (`class` vs `struct`, missing `_version`,
`SdnTable`/`SdnDatabase` shapes, and a `test.lib.database_fixtures` module that
must be confirmed to exist), so the file needs a genuine rewrite against
`std.database.core` and will very likely expose real, previously-hidden
failures. That is a database-lane change, not a compiler-integration one, and
doing it blind inside a timeboxed measurement lane risks trading one vacuous
spec for a differently-vacuous one.

Do **not** "fix" the 11 red examples by adding `has_column` to the stub — that
would deepen the vacuity. The fix is to delete the stubs and import the subject.
