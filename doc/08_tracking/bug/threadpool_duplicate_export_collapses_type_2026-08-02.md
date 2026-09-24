# Two exported classes named ThreadPool collapse into a type with neither API

- **Date:** 2026-08-02
- **Status:** RESOLVED (2026-09-13) — see Fix landed below.
- **Severity:** HIGH — a name collision between two exported classes silently
  produces an unusable type instead of an error or a correct resolution. An
  explicit module-qualified import does not save you.
- **Found by:** de-vacuifying `async_file_spec.spl`, whose 17 examples were all
  `pass`.
- **Component:** `src/lib/nogc_async_mut/io/file.spl`,
  `src/lib/nogc_async_mut/thread_pool.spl`, and the module/export resolver.

## Claim

Two different classes named `ThreadPool` are exported into the
`std.nogc_async_mut` namespace. Importing either one yields a type that has
**neither class's members**. PROVED.

## The two definitions

| Source | Shape | Re-exported by |
|---|---|---|
| `io/file.spl:219` | `class ThreadPool { size: i64 }` with `new(size)`, `default()`, `exec(task)` | `io/__init__.spl:77` |
| `thread_pool.spl:16` | `class ThreadPool` with `new(num_workers)`, `default()`, `pending_tasks()`, `is_idle()`, `is_shutdown()` | `__init__.spl:183` |

## Reproduction — PROVED

With an explicit, fully module-qualified import of the `io/file.spl` one:

```
use std.spec
use std.nogc_async_mut.io.file.{ThreadPool}

describe "ThreadPool identity, no nested calls":
    it "pending_tasks via a bound local (thread_pool.spl API)":
        val p = ThreadPool.new(7)
        val n = p.pending_tasks()
        expect(n).to_equal(0)
    it "is_idle via a bound local (thread_pool.spl API)":
        val p = ThreadPool.new(7)
        expect(p.is_idle()).to_equal(true)
    it "size via a bound local (io/file.spl API)":
        val p = ThreadPool.new(7)
        expect(p.size).to_equal(7)
```

All three fail:

```
semantic: method `pending_tasks` not found on type `ThreadPool`
semantic: method `is_idle` not found on type `ThreadPool`
semantic: undefined field 'size': cannot access field on value of type 'thread_pool'
```

`ThreadPool.new(7)` itself **succeeds** — construction works. The resulting
value simply has no reachable members from either definition. The third message
also shows the type printing as lowercase `thread_pool`, i.e. the module name,
not either class.

So this is not last-wins resolution, which would at least give a usable class.
It is a degenerate merge that type-checks at the constructor and then rejects
every member access.

Each example above was run through a bound local specifically to rule out the
separate "nested call context" method-lookup limitation, which produced a
different and misleading message on the first attempt.

## Why this went unnoticed — PROVED

`async_file_spec.spl` had 17 examples, all shaped like:

```
it "documents thread pool creation":
    # val pool = ThreadPool.new(4)
    # val result = await pool.spawn(\: expensive_computation())
    pass
```

Every intended call was a comment; the executed body was `pass`. The file
imported nothing. 17 green examples, zero coverage, and the collision sat
undetected.

Proof the old file could not detect a regression here, sabotaging the shipped
`errno_to_io_error` so ENOENT maps to `PermissionDenied`:

| | clean impl | sabotaged impl |
|---|---|---|
| **pristine spec (17 `pass`)** | GREEN | **GREEN, 0 failures** |
| **repaired spec (14 examples)** | GREEN | **RED, 2 failures** |

Control `rvv_misc_spec.spl` stayed GREEN throughout; restoring returned green.

## Fix required

1. Rename one of the two classes, or stop re-exporting one of them, so a single
   `ThreadPool` is reachable from `std.nogc_async_mut`.
2. Make a duplicate exported type name a **hard error** at module-resolution
   time. Silently producing a memberless type is the worst outcome: it
   type-checks far enough to construct, then fails at every use, and the error
   message names the module rather than either class.
3. Sweep for other duplicate exported names in the same namespace. This one was
   found by accident; INFERRED, not proved, that there are more.

## Note on coverage

`async_file_spec.spl` deliberately does not cover `ThreadPool` and says so in
place, so the omission is not mistaken for a fresh placeholder. Add coverage
once a single `ThreadPool` is reachable. The async read/write paths
(`AsyncFile.open/read/write/fsync`) are also uncovered because they take an
`IoDriver` and resolve through the event loop, which an in-process spec cannot
reach.

## Related

- `doc/08_tracking/bug/vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02.md`
- `doc/08_tracking/bug/gc_analysis_desugar_dropped_method_bodies_2026-08-02.md`
- `doc/08_tracking/bug/unify_occurs_check_unreachable_2026-08-02.md`

## Fix landed (2026-09-13, BUGFIX-11)

Applied fix option 1 from "Fix required" above: renamed
`src/lib/nogc_async_mut/io/file.spl`'s `class ThreadPool` to
`class FileThreadPool`, so a single `ThreadPool` (the `thread_pool.spl` real
worker pool) is reachable everywhere; the io/file fallback pool keeps its own
distinct API under its own name. Updated every facade that names it by bare
import so no stale reference to the old name remains:

- `src/lib/nogc_async_mut/io/file.spl` (definition, `new`/`default`, export)
- `src/lib/nogc_async_mut/io/__init__.spl:77`
- `src/lib/nogc_async_mut/io.spl:92,119`
- `src/lib/nogc_sync_mut/io.spl:121,157`
- `src/lib/nogc_sync_mut/__init__.spl:204`
- `src/lib/gc_async_mut/io.spl:92,126`
- `src/lib/gc_async_mut/io/file.spl:10`

`grep -rn '\bThreadPool\b' --include=*.spl src/lib` confirms the only
remaining bare `ThreadPool` references are `thread_pool.spl` itself and
`nogc_async_mut/__init__.spl:178` (which exports the real one, unaffected).

**RED (before fix, exact doc reproduction):**
`test/01_unit/lib/nogc_async_mut/io/threadpool_duplicate_export_repro_spec.spl`
(originally the doc's own three examples, importing
`std.nogc_async_mut.io.file.{ThreadPool}`) — `3 examples, 3 failures`,
matching the doc's `method ... not found` / `undefined field 'size'`
messages exactly.

**GREEN (after fix):** the spec was updated to import `FileThreadPool` (the
renamed symbol) and to check both class declarations remain distinct by
name via `read_file_text` — `bin/simple test
test/01_unit/lib/nogc_async_mut/io/threadpool_duplicate_export_repro_spec.spl`
-> `3 examples, 0 failures`, `PASS`.

**Regression check:** `test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl`
(17 examples), `thread_pool_spec.spl` (6 examples), and
`thread_pool_state_contract_spec.spl` (3 examples) all still PASS.
`thread_pool_authority_spec.spl` fails, but pre-existing and unrelated: it
does a text match against `thread_pool.spl` (untouched by this change) and
that file's content already contains every string the spec asserts, so the
failure is a pre-existing brittle-match issue in the spec itself, not a
regression from this fix.

Not fixed here (out of scope, per "Fix required" item 2/3): making a
duplicate exported class name a hard error at module-resolution time, and a
repo-wide sweep for other same-name collisions. Both remain open follow-ups.
