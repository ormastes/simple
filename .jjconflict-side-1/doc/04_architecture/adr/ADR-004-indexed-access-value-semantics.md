# ADR-004: Indexed access yields a value; in-place mutation through it is not guaranteed

**Status:** accepted (2026-07-31)
**Context doc:** `doc/08_tracking/bug/mutate_through_index_loses_write_2026-07-31.md`

## Problem

`container[key].push(x)` behaves differently per engine and statement scope.
Probed 2026-07-31:

| Context | `run` engines (JIT / interp-mode / native) | `bin/simple test` runner |
|---|---|---|
| top-level statements | dict-index and tuple/struct-field writes **lost** | n/a |
| inside a `fn` | writes reach the container | dict-index and tuple/struct-field writes **lost** |

Plain array-of-arrays (`b[i].push(x)` on `[[T]]`) mutates in place on every
engine and scope. 17 real call sites (6 in `src/lib`, 11 in
`src/app`/`src/compiler`) silently depended on the losing shapes.

## Decision

**Value semantics is the language contract.** Indexing a Dict, or reaching a
tuple/struct field of an indexed element, yields a *value*; calling a mutating
method on that value does not update the container. This matches the standing
"arrays are value types" doctrine and requires zero engine work.

Guaranteed idioms:

- **Write-back** (the only portable mutation form for dict values and
  tuple/struct fields):
  `var bucket = c[k]; bucket.push(x); c[k] = bucket`
- **Array-of-arrays direct element mutation** (`b[i].push(x)` on `[[T]]`) — all
  engines agree, and stdlib code (`group_by`) now relies on it.
- Compound-assignment lvalue paths (`d[k].f = v`, `x[i].n = x[i].n + 1`) are
  writes to an lvalue, not method calls on a temporary, and stay valid.

Explicitly NOT guaranteed: relying on the in-function reference behaviour the
`run` engines currently exhibit. That behaviour is tolerated (engines need not
change) but code must not depend on it; the write-back is a redundant
self-assignment there, so conforming code is correct on every engine.

## Consequences

- All 17 audited sites use write-back (src/lib landed `49fff59485d5`; the 11
  app/compiler sites land with this ADR).
- Follow-up feature request: a lint (COLL family, alongside
  `collection_patterns.spl`) flagging a mutating-method call whose receiver is
  a dict index or an indexed tuple/struct field — the pattern is silent and
  invisible to the reader. Tracked in the collection-planner plan
  (`doc/03_plan/agent_tasks/collection_planner_parallel_agents_2026-07-31.md`).

## Rejected alternative

Declaring reference semantics and fixing the test-runner engine + top-level
handling to match. Rejected: contradicts value-type doctrine, requires changes
in two known-fragile engine paths, and every existing correct call site already
uses the write-back idiom.
