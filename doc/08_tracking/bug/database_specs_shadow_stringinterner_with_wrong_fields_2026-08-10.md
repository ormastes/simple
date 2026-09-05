# Four database specs shadow StringInterner with incompatible field sets

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Files**:
  - `test/integration/compiler/core_intensive_spec.spl:17` (fields `strings`, `reverse`, `next_id: i64`)
  - `test/integration/lib/database_core_spec.spl:30` (same wrong field set)
  - `test/unit/lib/database/database_core_spec.spl:51` (same wrong field set)
  - `test/unit/lib/database/database_spec.spl:15` (closer: `str_to_id`, `id_to_str`, but `next_id: i64` instead of `StringId`)
- **Real product code**: `src/lib/nogc_sync_mut/database/core.spl:52` — `class StringInterner`
  with fields `str_to_id: Dict<text, StringId>`, `id_to_str: Dict<StringId, text>`,
  `next_id: StringId` (a wrapper class, not a bare `i64`).
- **Found during**: continuation of the SHADOW-family spec vacuity sweep
  (worklist rows 10, 11, 91, 92 in `spec_shadow_reimplementation_worklist.tsv`).

## What's wrong

All four specs declare `# use std.database.core.{StringInterner, ...}` **only
in a comment**, then define a local `StringInterner` class instead of
importing the real one. Three of the four (`core_intensive_spec`,
`database_core_spec` ×2) use completely different field names
(`strings`/`reverse`) that don't exist on the real type at all — an
import-swap would not compile without a full rewrite of every
`StringInterner(...)` construction site (9-13 call sites per file) and every
field access. The fourth (`database_spec.spl`) is closer (same field names)
but still incompatible: `next_id` is typed `i64` locally vs. the real
`StringId` class, so even its constructors (`StringInterner(str_to_id: {},
id_to_str: {}, next_id: 0)`) would fail to typecheck against the real class
without wrapping every `next_id` in `StringId(value: ...)`.

None of the four specs can catch a real defect in
`src/lib/nogc_sync_mut/database/core.spl` — they only ever exercise their own
local reimplementation, which drifted from the real API (the real class also
carries `SdnDatabase`/`SdnTable`/WAL-related behavior not modeled locally at
all).

## RESOLVED 2026-08-10 — all four rewritten against the real type

All four specs now import the real `StringInterner` from
`src/lib/nogc_sync_mut/database/core.spl`; the local fakes are deleted. Both
duplicate tree legs were verified identical before and after and are fixed
together. Verdict lines below are from `bin/simple test <path>`.

| # | spec | legs | verdict | outcome | commit |
|---|------|------|---------|---------|--------|
| 1 | `compiler/core_intensive_spec.spl` | `test/integration` + `test/02_integration` | 32 total, 29 passed, 3 failed | fixed (interner tests all green; 3 failures PRE-EXISTING, identical on parent) | `7c43f6e8c10` |
| 2 | `lib/database_core_spec.spl` | `test/integration` + `test/02_integration` | 35 total, 35 passed, 0 failed | fixed, fully green | `b95b116c04a` |
| 3 | `lib/database/database_core_spec.spl` | `test/unit` + `test/01_unit` | 35 total, 35 passed, 0 failed | fixed, fully green | `9cc848b84ac` |
| 4 | `lib/database/database_spec.spl` | `test/unit` + `test/01_unit` | 27 total, 27 passed, 0 failed (was 26/1) | fixed, `from_sdn` id-0 defect FIXED (see below) | `ac40801103b` (spec) + follow-up (fix) |

Specs 2, 3 and 4 also had local fake `SdnRow`/`SdnTable` classes; those were
removed too, since the real `from_sdn`/`to_sdn`/`valid_rows` tests cannot be
exercised without the real table types. The real `SdnTable` API turned out to
be a superset of each fake.

### Blocking finding: `from_sdn` silently drops id 0 — FIXED 2026-08-10

Rewriting spec 4 immediately surfaced a genuine product defect that the shadow
had been hiding for as long as it existed:

`StringInterner.from_sdn` guarded row loading with `if id > 0`, but `intern()`
hands out ids starting at **0**. So the **first string ever interned was lost
on every save/load round-trip**. Measured directly against the real type:
a table containing rows `(id=0,"test1")` and `(id=1,"test2")` loaded as
`get(0) -> Option::None`, `get(1) -> Option::Some(test2)`.

The removed local fake accepted id 0, which is exactly why no spec ever caught
this. Per the no-weakening rule the assertion was left intact and RED, with a
`FIXME` in place at the test.

**Fix chosen**: widen the guard to `if id >= 0` in
`src/lib/nogc_sync_mut/database/core.spl:113`, keeping `intern()` starting at
0 unchanged. Ruled out the alternative (`intern()` starting ids at 1) because:
no `.sdn` fixture, test data, or other call site in the repo depends on the
current 0-based numbering (`/usr/bin/grep -rn "from_sdn"` /
`"intern("` across `src/` and `test/` found no other consumer coupled to the
starting value), and no code near the interner treats id 0 as an
absent/sentinel marker — the other two `id > 0` hits in the database library
(`atomic.spl:167` process-id liveness check, `test_extended/factory.spl:141`
unrelated generic id filter) are unrelated to `StringInterner`. Widening the
guard is therefore the minimal, format-compatible fix.

**Verification**: round-trip of `{0: "test1", 1: "test2"}` through
`to_sdn()`/`from_sdn()` now returns both entries via `get(0)` and `get(1)`, per
the (unweakened) spec assertion. Both duplicate-tree legs
(`test/01_unit/lib/database/database_spec.spl`,
`test/unit/lib/database/database_spec.spl`) now pass fully: **27 total, 27
passed, 0 failed** (previously 26 passed / 1 failed, matching the pinned
baseline). Negative control: reverting the guard back to `if id > 0` and
re-running reproduces the pinned failure exactly — "loads from SDN table" is
the sole failing example, 26/27 — confirming the assertion is not vacuous
before the fix was reapplied. The FIXME comment in both legs of
`database_spec.spl` was replaced with a RESOLVED note; the assertion itself
(`check(interner.get(0)? == "test1")`) was not weakened, only the guard
comment/status changed.

### Remaining sibling shadows (tracked, not silently accepted)

`test/integration/compiler/core_intensive_spec.spl` still declares local fake
`SdnRow`/`SdnTable`. Its fake `SdnTable` is `schema`-based and structurally
unrelated to the product `SdnTable` (`columns`/`index`), so it is not a bounded
import swap. Its 3 pre-existing failures live in those stub tests.

That file's fake `StringInterner` had also **inverted** the API: its
`get(s: text)` was the forward string->id lookup, whereas the product `get(id)`
is the reverse id->string lookup and the forward one is `get_id`. Call sites
were remapped to the real meaning, matching the test's own
`# Forward lookup: string -> id` comment.

## Why it was not fixed in the filing pass (historical)

Same class of finding as `narrowing_spec`/`riscv_dual_arch_spec`/
`type_infer_correctness_spec`: 3 of 4 files need every constructor site and
field access rewritten against a differently-named field set (not a bounded
import swap), and the 4th needs every `next_id: <int>` call site changed to
`next_id: StringId(value: <int>)` plus verification that `Dict<StringId,
text>`/`Dict<text, StringId>` keying still behaves as the specs assume.

## Unblock condition

Rewrite each of the four specs against the real
`src/lib/nogc_sync_mut/database/core.spl` `StringInterner` (real field names,
`StringId`-typed `next_id`), re-run, and confirm the assertions still hold
against the real intern/lookup/`from_sdn` behavior — not just that
construction typechecks.
