# `nogc_async_mut_noalloc/collections/*` claim "no heap allocation" but are backed by a real heap `[T]` array — partially fixed, root cause stays open

**Filed:** 2026-08-07
**Severity:** high — undermines the allocation-class lattice (WP-12) the whole
Wave-3 aerospace plan depends on
**Status:** PARTIALLY FIXED — steady-state (post-construction) heap growth
eliminated for `FixedArray`/`FixedStack`, and per-operation object allocation
eliminated for `FixedMap`; genuine inline/static storage is **not
achievable** with the language as it exists today. Stays RED.

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
| `FixedMap` | `entries: [FixedMapEntry]` | `probes < capacity` linear-probe scan; full map returns `false` | `new()` pre-fills `entries` to full `capacity` **once** — but every `put()` insert (`:65`), every `put()` update (`:70`), and up to 3 sites per `remove()` (`:116`, `:126-130`, `:131`) called `FixedMapEntry(...)` — **a real per-operation heap allocation** (class instantiation, `new` is the first tag in the noalloc checker's own `DirectAlloc` list). This is the same defect class as `FixedArray`/`FixedStack`, just expressed as object churn instead of array growth — the original table entry calling this "already correct" was wrong | `fixed_map.spl:40-47,:65,:70,:116,:126-131` (pre-fix) |
| `FixedSet` | `keys: [i64]`, `occupied: [bool]` | `probes < cap` linear-probe scan; full set returns `false` | Same pre-fill-once-at-construction pattern as `FixedMap`; `add()`/`remove()` only index-assign | `fixed_set.spl:30-39` (unchanged, already correct) |
| `RingBuffer` | `data: [i64]` | `count >= capacity` check before insert (already correct) | Same pre-fill-once-at-construction pattern; `enqueue()`/`dequeue()`/`clear()` only index-assign or touch `head`/`tail`/`count`, never `data` | `ring_buffer.spl:29-47` (unchanged, already correct) |

**Correction to the manifest bug's framing:** not all five types had the same
defect, and an earlier revision of this table wrongly cleared `FixedMap`.
`FixedSet`/`RingBuffer` reserved their backing array once at construction and
never allocated again — a real heap allocation, but a single one at `new()`,
not per-operation; those two needed no fix. `FixedArray` and `FixedStack`
grew their backing array on **every** `push()` call (still capped at
`capacity` calls total — the pre-existing `len >= capacity` / `top >=
capacity` guard was already correct, over-capacity insert was never silently
accepted). `FixedMap` reserved its backing array once but then allocated a
new `FixedMapEntry` object on **every** `put()`/`remove()` call — a third,
distinct shape of the same underlying defect.

**`PoolLinkedList` (`linked_list.spl`, same directory, exported from the same
`__init__.spl`, not one of the task's five) looked correct by inspection
(construct-once node pool, index-based mutation) but is separately, severely
broken at runtime** — see "Unrelated defect surfaced while investigating a fix
shape" below. Not fixed here (outside this bug's scope and outside the
`nogc_async_mut_noalloc/collections` library — the root cause is an
interpreter limitation).

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

**Risk assessment for the landed fix:** `FixedArray`/`FixedStack`/`FixedMap`
all have zero production consumers, so their allocation-timing/shape changes
land on nobody currently depending on the old behaviour. `RingBuffer`'s one
production consumer (`scheduler.spl`) was already using the correct
construct-once pattern and is untouched by this fix.

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

`src/lib/nogc_async_mut_noalloc/collections/fixed_map.spl`: refactored from
`entries: [FixedMapEntry]` (array-of-struct) to parallel primitive arrays
`keys: [i64]`, `values: [i64]`, `occupied: [bool]` — the pattern `FixedSet`
already used successfully. `put()`/`remove()` now write by plain index
assignment (`self.keys[idx] = key`); no entry object is ever constructed
after `new()`. The `FixedMapEntry` class is removed (zero consumers besides
the `__init__.spl` re-export chains, which were updated:
`src/lib/nogc_async_mut_noalloc/collections/__init__.spl`,
`src/lib/nogc_async_mut_noalloc/__init__.spl`).

**Why not mutate `FixedMapEntry` in place instead of removing it?** Tried
first (`self.entries[idx].key = key`) and rejected by the interpreter:
`semantic: invalid assignment: complex indexed field receiver is not
supported`, reproduced with a minimal throwaway probe. See the
`PoolLinkedList` section below — this is a real interpreter limitation, not
specific to `FixedMap`, so the parallel-array refactor (which uses only
plain, non-field index assignment, already proven to work by the
`FixedArray`/`FixedStack` fix above) was used instead.

Permanent spec:
`test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl`
— `Results: 3 total, 3 passed, 0 failed`. Pre-existing `fixed_map_spec.spl`
(both `test/01_unit/...` and `test/unit/...` copies) is a local-replica spec
that defines its own `FixedMap` class rather than importing the real module
(same pattern noted for `noalloc_checker_spec.spl` in the WP-11 fix) — it
does not exercise the real implementation and stayed green
(`11 passed`) because it never could have failed on this axis.

Also corrected the false "no heap allocation" claim in `ring_buffer.spl`'s
header (it allocates once at construction, not zero times), the false
"lowers to stack-allocated storage" claim in `fixed_array.spl`'s header (no
evidence this ever happens — see below), and the family-wide "Heap-Free" /
"no dynamic allocation" claim in `collections/__init__.spl`'s header.
`fixed_set.spl`'s header gained the same inline-storage-gap pointer the
other four now carry.

## Unrelated defect surfaced while investigating a fix shape

While looking for a way to eliminate `FixedMap`'s per-operation allocation
without a full parallel-array refactor, tried the in-place field-mutation
pattern `PoolLinkedList` (`linked_list.spl`, same directory) appears to use:
`self.nodes[idx].next = next_free`, `self.nodes[idx].value = value`, etc.
(`linked_list.spl:71-73,78-81,88-90,...`).

**That pattern does not work.** Reproduced two ways:

1. A minimal throwaway class (`Holder` with `slots: [Slot]`, a `me
   set_via_field_write(idx, ...)` method doing `self.slots[idx].key = k`)
   fails at `bin/simple test` time with `semantic: invalid assignment:
   complex indexed field receiver is not supported`.
2. **The real, shipped `PoolLinkedList.push_back` fails identically** when
   actually exercised: `val list = PoolLinkedList.new(4); list.push_back(10)`
   raises the same `complex indexed field receiver is not supported` error
   and the spec fails outright.

`test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl`
is a text-scan spec (asserts on method signatures in the source text, never
calls `push_back`/`push_front`/`pop_front`/etc.), so this defect has been
invisible to the test suite. **`PoolLinkedList`'s core operations
(`push_front`, `push_back`, `pop_front`, `pop_back`, `remove_at` — anything
that calls `alloc_node()`/`free_node()`) are non-functional at runtime.**

Not fixed here: out of scope for this bug (root cause is an interpreter
limitation in `src/compiler/**`, which this investigation's scope excludes),
and a distinct defect class (correctness, not allocation). Filing this
finding here rather than silently leaving it invisible; a dedicated bug
record for the interpreter limitation itself is recommended as a follow-up
before `linked_list.spl` is trusted or extended.

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
3. Separately, fix or replace the interpreter limitation behind "complex
   indexed field receiver is not supported" (evidenced above by both a
   minimal probe and `PoolLinkedList.push_back` failing at runtime) — that
   is a distinct, higher-priority defect since it makes shipped code
   non-functional, not just non-optimal.
4. Until both land, this doc's "PARTIALLY FIXED" status is accurate:
   steady-state (post-construction) allocation is eliminated for all five
   types (`FixedSet`/`RingBuffer` already had it; `FixedArray`/`FixedStack`
   gained it via eager reservation; `FixedMap` gained it via the
   parallel-array refactor), but construction-time allocation is real and
   the manifest cannot yet express that distinction (same gap noted in the
   WP-11 fix for `mimalloc`/`baremetal.allocator`).

Tracked as WP-12 input in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.
