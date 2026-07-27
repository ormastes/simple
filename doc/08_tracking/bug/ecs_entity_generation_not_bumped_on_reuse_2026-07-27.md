---
id: ecs_entity_generation_not_bumped_on_reuse_2026-07-27
status: OPEN
severity: high
discovered: 2026-07-27
discovered_by: lane SPECM — exposed after fixing the matcher shape in test/01_unit/lib/ecs/ecs_spec.spl
related: src/lib/nogc_sync_mut/ecs/entity.spl
related: src/lib/nogc_async_mut/ecs/entity.spl
related: test/01_unit/lib/ecs/ecs_spec.spl
---

# EntityAllocator does not bump the generation on slot reuse — stale handles alias

## Symptom

`test/01_unit/lib/ecs/ecs_spec.spl` — "bumps generation on reuse so stale handles
do not alias":

```
expected true to equal false      # expect(alloc.is_live(a)).to_equal(false)
```

Probe (`build/specm_repro/h_spec.spl`), after `a = alloc()`, `free(a)`, `b = alloc()`:

```
a.id=0 a.gen=1
b.id=0 b.gen=1        <- must be 2
freed=true
is_live(a)=true       <- stale handle still live
```

This was previously masked: the assertion used the broken shape
`expect alloc.is_live(a).to_equal(false)`, which died with
`method 'to_equal' not found ... in nested call context`
(see `spec_matcher_nested_call_dispatch_2026-07-27`), so the example was red for
a harness reason and nobody looked past it.

## Root cause

`src/lib/nogc_sync_mut/ecs/entity.spl`. The `generations[]` array is overloaded:
it stores the live generation for a slot *and*, once freed, the negated free-list
link. Freeing therefore **destroys** the generation:

- `me free`: `self.generations[e.id] = -(prev_free + 1)` — original generation gone.
- `me alloc` reuse path: `self.generations[id] = (-self.generations[id] + 1)` —
  this is `-(link) + 1`, i.e. it reconstructs a value from the *free-list link*,
  not from the previous generation.

For the first slot: gen 1 -> free stores `-(-1+1) = 0` -> realloc computes
`-0 + 1 = 1`, the same generation. The stale handle matches and `is_live` returns
true. The doc comment on the struct ("the generation bumps on reuse so stale
handles do not alias") is not what the code does.

`src/lib/nogc_async_mut/ecs/entity.spl` carries the same implementation.

## Fix sketch (NOT applied — `src/lib/*/ecs/**` is outside lane SPECM's scope)

Stop overloading one array. Keep `generations: [i32]` monotonic (bump on free or
on reuse) and hold the free list in its own `free_slots: [i32]` array, so the
generation is never clobbered by a link value.

Regression already in place: the assertion in
`test/01_unit/lib/ecs/ecs_spec.spl` is now in canonical form and fails honestly.
Do not weaken it.
