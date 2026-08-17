---
id: ecs_entity_generation_not_bumped_on_reuse_2026-07-27
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
fixed: 2026-07-27
fixed_by: lane ECSGEN
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

## Fix (applied 2026-07-27, lane ECSGEN)

`EntityAllocator` no longer overloads one array. Applied identically to all
three ECS trees (`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/ecs/`) —
`use std.ecs.*` resolves to `nogc_async_mut`, so a one-tree fix is invisible.

- `generations[id]` holds only the generation. Monotonic per slot: `free` bumps
  it, `alloc` never touches it. Slot generations start at 1; generation 0 stays
  reserved for `Entity.null()` and for `with_capacity` reservation padding.
- `next_free[id]` is a new array holding only the free-list link / slot state:
  `-2` LIVE, `-3` RETIRED, `-4` RESERVED, `-1` free/end-of-list, `>=0` free with
  a link to the next free slot.
- `is_live(e)` requires BOTH `next_free[e.id] == LIVE` and
  `generations[e.id] == e.generation`. The state half stops a fabricated handle
  from validating against a freed-but-unreused slot; the generation half stops a
  reused slot from accepting an old handle. `Entity.null()` (id `-1`) still
  fails the range check.
- **Wraparound policy: generations never wrap.** When a slot's generation
  reaches `gen_cap` (i32 max), `free` RETIRES the slot — it is withdrawn from
  circulation for the life of the allocator and counted by `retired_slots()` —
  instead of recycling it. A bounded id leak is traded for the guarantee that a
  generation value is never reissued for a slot. `with_generation_cap(cap)`
  lowers the cap so the policy is testable without 2^31 frees.
- `ComponentStore` is keyed by `e.id` alone and `src/os/**` deliberately
  fabricates `Entity(id: n, generation: 0|1)` handles for store lookups, so the
  store was NOT made generation-strict. Instead it gained additive checked
  accessors — `get_slot_checked(e, alloc)` and `contains_live(e, alloc)` —
  which reject stale handles. Callers whose handles can outlive a despawn must
  use these; the raw `get_slot`/`contains` still alias by design.

Verified: `test/01_unit/lib/ecs/ecs_spec.spl` 16 examples / 0 failures across
all 5 describe blocks, in both default and `SIMPLE_EXECUTION_MODE=interpreter`.
No regressions in `test/01_unit/os/services/{ds,devfs,pipefs,procfs,rs,clock,sched}_service_spec.spl`,
`.../container/container_manager_spec.spl`, `.../tty_termios_ld_spec.spl`,
`.../wm/wm_world_multi_window_identity_spec.spl` (all 0 failures).
