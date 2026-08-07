# `PoolLinkedList.push_back`/`push_front` (and everything using `alloc_node`/`free_node`) fails at runtime — interpreter rejects indexed-field assignment

**Filed:** 2026-08-07
**Severity:** high — shipped, exported code is non-functional; masked by a
text-scan-only spec
**Status:** OPEN — root cause is an interpreter limitation in
`src/compiler/**`, out of scope for this record (filed from
`src/lib/nogc_async_mut_noalloc/collections/**`, which this record's scope
covers)

## Origin

Surfaced as a side-finding while investigating a fix shape for
`doc/08_tracking/bug/noalloc_collections_backed_by_growable_heap_array_2026-08-07.md`
(the `FixedMap` per-operation allocation fix). Filed as its own record per
that doc's note that this finding is more severe (correctness, not
allocation efficiency) and would not be discoverable under a filename about
heap growth.

## Repro

`src/lib/nogc_async_mut_noalloc/collections/linked_list.spl`'s
`PoolLinkedList` mutates pool nodes through an array-indexed field write,
e.g. `alloc_node()`:

```
me alloc_node() -> i32:
    if self.free_head == -1:
        return -1
    val idx = self.free_head
    self.free_head = self.nodes[idx].next
    self.nodes[idx].next = -1      # <-- indexed field write
    self.nodes[idx].prev = -1      # <-- indexed field write
    idx
```

The same pattern appears at `linked_list.spl:78-81` (`free_node`), `:88-90`
(`push_front`), `:104-106` (`push_back`), and elsewhere in the file —
`self.nodes[idx].value = value`, `self.nodes[idx].next = ...`, etc.

Minimal reproduction (throwaway probe, not committed):

```
class Slot:
    key: i64
    value: i64
    occupied: bool

class Holder:
    slots: [Slot]
    ...
    me set_via_field_write(idx: i32, k: i64, v: i64):
        self.slots[idx].key = k        # fails
```

Running through `bin/simple test`:

```
semantic: invalid assignment: complex indexed field receiver is not supported
```

**Confirmed on the real, shipped type, not just the minimal repro** —
`val list = PoolLinkedList.new(4); list.push_back(10)` through `bin/simple
test` produces the byte-identical error:

```
✗ checks whether push_front/pop_front work (exercises self.nodes[idx].field = v)
    semantic: invalid assignment: complex indexed field receiver is not supported
1 example, 1 failure
```

So `PoolLinkedList.push_back`, `push_front`, `pop_front`, `pop_back`, and
`remove_at` — every operation that calls `alloc_node()` or `free_node()` —
fail immediately at runtime with this error. The type is exported
(`collections/__init__.spl:30`, re-exported from
`nogc_async_mut_noalloc/__init__.spl`) and documented as working
(`linked_list.spl:1-11` gives a `push_back`/`push_front`/`pop_front` usage
example) but cannot actually run any of those operations.

## Why this was invisible

`test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl`
(both the `test/01_unit/...` and `test/unit/...` copies) is a text-scan
spec: it reads the source file as text and asserts on method signatures
(`expect(source).to_contain("me push_back(value: i64) -> bool")`), and never
imports or calls the real `PoolLinkedList`. `Results: 2 total, 2 passed, 0
failed` on this spec proves nothing about whether `push_back` executes.

## Consumers

`grep -rl 'PoolLinkedList'` across `src/` and `test/` finds only the defining
file and the two `__init__.spl` re-export chains — **zero other consumers**,
production or test. Nothing currently depends on this working, which is
presumably why it has gone unnoticed.

## Unblock condition

Root-cause the interpreter's rejection of `self.<array_field>[idx].<field> =
value` (nested field assignment through an array-indexed receiver) in
`src/compiler/**` — outside this record's scope (this session's task was
scoped to `src/lib/nogc_async_mut_noalloc/collections/**`, not the
compiler). Once fixed, add a real (non-text-scan) regression spec that
imports `PoolLinkedList` and exercises `push_back`/`push_front`/`pop_front`/
`pop_back`/`remove_at`, proving each was broken before and works after —
the same before/after discipline used in the sibling `FixedArray`/
`FixedStack`/`FixedMap` fixes.

Tracked as WP-12 input in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.
