# Two exported classes named ThreadPool collapse into a type with neither API

- **Date:** 2026-08-02
- **Status:** OPEN
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
