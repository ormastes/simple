# `nogc_async_mut_noalloc/collections/*` claim "no heap allocation" but are backed by a real heap `[T]` array — partially fixed, root cause stays open

**Filed:** 2026-08-07
**Severity:** high — undermines the allocation-class lattice (WP-12) the whole
Wave-3 aerospace plan depends on
**Status:** PARTIALLY FIXED — steady-state (post-construction) heap growth
eliminated for `FixedArray`/`FixedStack`; genuine inline/static storage is
**not achievable** with the language as it exists today. Stays RED.

## Origin

Surfaced by WP-12a while landing
`doc/08_tracking/bug/noalloc_family_manifest_prefix_match_exempts_its_own_allocators_2026-08-07.md`
(see that doc's final section, "Second real finding, out of scope for this
WP"). Referenced from
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md` Wave 3
(WP-12/WP-12a rows).

## Per-type measurement (before fix)

All five files in `src/lib/nogc_async_mut_noalloc/collections/` claimed
"no heap allocation" / "no heap growth" in their header comments. Measured
directly (not from the doc comments):

| Type | Backing field | Capacity enforced | Growth pattern (measured) | file:line |
|---|---|---|---|---|
| `FixedArray` | `items: [i64]` | `len >= capacity` check before insert (already correct) | Started `items: []` (len 0) in `new()`; **every `push()` called `.items.push(value)`** — real per-call heap growth up to `capacity` calls; `clear()` did `self.items = []` (dealloc) | `fixed_array.spl:27-37` (pre-fix), `:65-68` |
| `FixedStack` | `items: [i64]` | `top >= capacity` check before insert (already correct) | Same pattern as `FixedArray`: `new()` started empty, `push()` called `.items.push(value)`, `clear()` did `self.items = []` | `fixed_stack.spl:26-36` (pre-fix), `:64-67` |
| `FixedMap` | `entries: [FixedMapEntry]` | `probes < capacity` linear-probe scan; full map returns `false` | `new()` pre-fills `entries` to full `capacity` via a `.push()` loop **once**; `put()`/`remove()` only do `self.entries[idx] = ...` (index assignment) — no further growth after construction | `fixed_map.spl:40-47` (unchanged, already correct) |
| `FixedSet` | `keys: [i64]`, `occupied: [bool]` | `probes < cap` linear-probe scan; full set returns `false` | Same pre-fill-once-at-construction pattern as `FixedMap`; `add()`/`remove()` only index-assign | `fixed_set.spl:30-39` (unchanged, already correct) |
| `RingBuffer` | `data: [i64]` | `count >= capacity` check before insert (already correct) | Same pre-fill-once-at-construction pattern; `enqueue()`/`dequeue()`/`clear()` only index-assign or touch `head`/`tail`/`count`, never `data` | `ring_buffer.spl:29-47` (unchanged, already correct) |

**Correction to the manifest bug's framing:** not all five types had the same
defect. `FixedMap`/`FixedSet`/`RingBuffer` already reserved their backing
array once at construction and never grew it again — a real heap allocation,
but a single one at `new()`, not per-operation. Only `FixedArray` and
`FixedStack` grew their backing array on **every** `push()` call (still
capped at `capacity` calls total, since the pre-existing `len >= capacity` /
`top >= capacity` guard was already correct — over-capacity insert was never
silently accepted). `PoolLinkedList` (`linked_list.spl`, same directory,
exported from the same `__init__.spl`, not one of the task's five) already
follows the correct construct-once pattern too — checked as part of this
investigation, not itself defective.

**Capacity enforcement, all five: correct before and after this fix.**
Over-capacity insert was never silently accepted by any of the five types —
that guard predates this bug. The defect was entirely about *when* backing
storage is reserved (once at construction vs. on every operation), not
whether capacity was enforced.

## Consumers

Counted by `grep -rl '\bTypeName\b'` across `src/` and `test/`, excluding the
defining file and re-export chains (`__init__.spl`):

| Type | Real (non-test) production consumers | Test-only consumers |
|---|---|---|
| `FixedArray` | **0** | several remote-JIT/baremetal system specs (text-scan or fixture use) |
| `FixedStack` | **0** | none beyond its own unit spec |
| `FixedMap` | **0** | `test/03_system/feature/app/remote_baremetal/remote_baremetal_library_workload.spl` (fixture) |
| `FixedSet` | **0** | same fixture as above |
| `RingBuffer` | **1** — `src/os/realtime/scheduler.spl:7,13,25` (`ready_queues: [RingBuffer]`, one per priority level in the realtime scheduler) | several remote-JIT/baremetal system specs |

Note: `src/lib/nogc_async_mut/compute/containers.spl` also defines a class
named `FixedArray<T>` — a **different type in a different tier**
(`nogc_async_mut`, not `nogc_async_mut_noalloc`), unrelated to this bug. Not
counted above.

**Risk assessment for the landed fix:** `FixedArray`/`FixedStack` have zero
production consumers, so switching their `new()` to eagerly reserve full
capacity (rather than growing lazily) changes allocation *timing* for nobody
currently depending on lazy growth. `RingBuffer`'s one production consumer
(`scheduler.spl`) was already using the correct construct-once pattern and is
untouched by this fix.

## Fix landed (2026-08-07)

`src/lib/nogc_async_mut_noalloc/collections/fixed_array.spl` and
`fixed_stack.spl`: `new()` now pre-reserves the backing `[i64]` array to full
`capacity` (a loop of `.push(0)`, matching the pattern `FixedMap`/`FixedSet`/
`RingBuffer` already use); `push()` writes by index
(`self.items[self.len] = value`) instead of calling `.items.push(value)`;
`clear()` resets the length/top counter only and no longer discards the
backing array (previously `self.items = []`, which forced the next `push()`
to reallocate from zero).

**Regression proof** — the discriminating axis is the backing array's real
length (`arr.items.len()`), not "over-capacity insert is rejected" (that was
never broken, asserting only on it would be a fail-open no-op spec):

- BEFORE: `FixedArray.new(8)` → `items.len() == 0`; after 3 pushes →
  `items.len() == 3`; after `clear()` → `items.len() == 0`. Measured directly
  via a throwaway probe spec run through `bin/simple test` before editing.
- AFTER: `items.len() == 8` at every stage — construction, after pushes,
  after `clear()`, after pushing again post-clear.

Permanent spec:
`test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_array_stack_backing_storage_regression_spec.spl`
— `Results: 4 total, 4 passed, 0 failed`.

Also corrected the false "no heap allocation" claim in `ring_buffer.spl`'s
header (it allocates once at construction, not zero times) and the false
"lowers to stack-allocated storage" claim in `fixed_array.spl`'s header (no
evidence this ever happens — see below).

## Why this stays RED — the missing language feature

The task target was "fixed-capacity storage that is genuinely
inline/statically reserved." That is **not achievable** in Simple today:

`src/compiler/10.frontend/core/parser.spl:781-798` — the parser accepts
sized-array type syntax `[T; N]` (kind 144, size-suffix kind 163) but
**discards the size expression**:

```
# Sized array type: [T; N] — accept and drop the size expression
# (stage4 arrays are dynamic; N is a literal or const ident).
kind = par_kind_get()
if kind == 163:
    parser_advance()
    for _si in 0..50:
        if par_kind_get() == 145 or par_kind_get() == 190:
            break
        parser_advance()
```

`[T; N]` and `[T]` both lower to the same dynamic-array type
(`TYPE_ARRAY_I64` etc.) — there is no way to declare a struct field as
inline, statically-sized storage that is part of the struct's own memory
layout rather than a separate heap allocation reached through a pointer.
Every `[T]` field in Simple, sized-annotation or not, is a heap array today.

This means the fix landed here **cannot** be extended to "zero heap
allocation, ever" for any of the five types without a new language feature:
inline fixed-size array storage embedded in a struct/class layout (the `[T;
N]` syntax already exists at the parse level and would be the natural
surface for it — it just needs to actually reserve `N` elements inline
instead of being discarded).

## Unblock condition

1. Add inline fixed-size array storage to the language: `[T; N]` as a struct
   field type must reserve `N` elements as part of the struct's own layout
   (stack-allocated when the struct itself is stack-allocated; embedded, not
   a separate heap pointer) rather than desugaring to `[T]`.
2. Once that exists, migrate `FixedArray`, `FixedStack`, `FixedMap`,
   `FixedSet`, `RingBuffer` (and `PoolLinkedList`, `linked_list.spl`, same
   family) to use it, and correct the manifest's `allocates` boolean per
   WP-12's five-class lattice — the `none` class becomes truthfully
   available for these types only after this lands.
3. Until then, this doc's "PARTIALLY FIXED" status is accurate: steady-state
   (post-construction) allocation is eliminated for all five types (three
   already had it; two gained it here), but construction-time allocation is
   real and the manifest cannot yet express that distinction (same gap noted
   in the WP-11 fix for `mimalloc`/`baremetal.allocator`).

Tracked as WP-12 input in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.
