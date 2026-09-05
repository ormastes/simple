# `core_intensive_spec.spl` is VACUOUS — it tests local stub classes, not `std.database.core`

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## Re-confirmation (2026-08-10)

Working copy still has the stubs and commented-out imports verbatim (`git show
origin/main:test/02_integration/compiler/core_intensive_spec.spl` matches the
dirty tree). Fresh execution:

```
bin/simple test test/02_integration/compiler/core_intensive_spec.spl
# Results: 32 total, 29 passed, 3 failed
# FAIL test/02_integration/compiler/core_intensive_spec.spl
#   semantic: method `has_column` not found on type `SdnRow`   (x2, "SdnRow - Intensive" block)
```

(Pass/fail counts drift run-to-run slightly from the 2026-08-04 figures —
32 total / 29 passed / 3 failed this run vs 21 passed / 11 failed originally
quoted — consistent with flaky ordering elsewhere in the suite, not with any
change to this file.)

Comparing the stub API against the real `std.database.core` module
(`src/lib/nogc_sync_mut/database/core.spl`) confirms the divergence is worse
than a single missing method, i.e. a real rewrite, not a patch:

* `StringInterner` stub fields: `strings: {text:i64}`, `reverse: {text:text}`,
  `next_id: i64`, constructed as a literal record
  `StringInterner(strings: {}, reverse: {}, next_id: 0)`.
  Real fields (`core.spl:52-56`): `str_to_id: Dict<text,i32>`,
  `id_to_str: Dict<i32,text>`, `next_id: StringId` (its own wrapper struct),
  constructed via `StringInterner.empty()`.
* Stub `interner.intern(s) -> i64`; real `me intern(s: text) -> i32`
  (`core.spl:62`).
* Stub `interner.get(s)` is the **forward** (string→id) lookup; the real API's
  `get(id: i32) -> text?` is the **reverse** lookup and forward is
  `get_id(s: text) -> i32?` (`core.spl:73,84`) — the method names are reused
  for the opposite direction, so a naive "just restore the `use` line" swap
  would compile-fail or, worse, silently invert semantics if signatures ever
  coincided.
* The commented-out fixture import path,
  `use test.lib.database_fixtures.{...}`, does not resolve to any file in the
  tree: no `test/lib/database_fixtures.spl` exists. The fixtures actually
  live at `test/feature/lib/database_fixtures.spl` (module path
  `test.feature.lib.database_fixtures`), which does export matching generator
  names (`generate_simple_row`, `generate_row_with_many_fields`, etc.) — so
  the rewrite also needs a corrected import path, not just an uncommented
  line.

## Why not fixed now

Restoring the real imports is the correct fix, but it is not a one-line change:
the stubs diverged from the real API (`class` vs `struct`, missing `_version`,
divergent field names/types, an inverted `get`/`get_id` method pairing, and a
`test.lib.database_fixtures` import path that must be corrected to
`test.feature.lib.database_fixtures`), so the file needs a genuine rewrite
against `std.database.core` and will very likely expose real, previously-hidden
failures. That is a database-lane change, not a compiler-integration one, and
doing it blind inside a timeboxed measurement lane risks trading one vacuous
spec for a differently-vacuous one — confirmed again on 2026-08-10 by directly
diffing the stub and real APIs above.

Do **not** "fix" the 3 (nee 11) red examples by adding `has_column` to the
stub — that would deepen the vacuity. The fix is to delete the stubs, correct
the fixture import path, rewrite the 32 examples against the real
`StringInterner`/`SdnRow`/`SdnTable` shapes (including the inverted
`get`/`get_id` naming), and move the file out of
`test/02_integration/compiler/` to a database-lane location, verifying with a
real `bin/simple test` run afterward since new failures are expected.

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN, and the exact mechanism is unchanged. Head of
`test/02_integration/compiler/core_intensive_spec.spl`:
```
5: # use std.database.core.{StringInterner, SdnTable, SdnRow, SdnDatabase}
6: # use test.lib.database_fixtures.{...}
7: fn check(condition: bool):
```
Both real imports are still commented out, and the file then defines its own
local `check`/`check_msg` helpers and stubs. Every example therefore exercises
spec-local code and can never fail on a `std.database.core` regression — a
vacuous-green spec of exactly the class this fleet is hunting.

### Scope note (lane I, 2026-08-17)
Not repaired here. Un-commenting :5-6 makes the spec depend on
`std.database.core` and `test.lib.database_fixtures`; whether those resolve is a
separate question from this lane`s slice, and a failed un-comment would leave
the file unloadable rather than merely vacuous. Recorded as verified-live.
