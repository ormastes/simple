# Lane ECSME — ECS `fn X(self)` → `me X()` conversion

## Root cause (reproduced)
`bin/simple run` on a probe importing `std.ecs.world`:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
cannot modify self in immutable fn method 'EntityAllocator.alloc'.
Use `me` instead of `fn` to allow self mutation
```

One bad method bails JIT lowering for the WHOLE program.

## Correct forms (confirmed from src/lib/nogc_sync_mut/buffer/types.spl)
- read-only:  `fn name(args) -> T:`   — NO explicit `self` param; `self.` usable in body
- mutating:   `me name(args) -> T:`   — NO explicit `self` param
- call sites unchanged: `obj.method(args)`

## IMPORTANT: three byte-identical ECS copies
`std.ecs.*` resolves to **`src/lib/nogc_async_mut/ecs/`** (default tier), NOT the
lane-owned `nogc_sync_mut` copy. All three trees are byte-identical:
- src/lib/nogc_sync_mut/ecs/   (lane-owned)
- src/lib/nogc_async_mut/ecs/  (the one actually resolved by `use std.ecs.*`)
- src/lib/gc_async_mut/ecs/
Fixing only the owned copy would NOT remove the bail. All three converted.

## Survey (29 methods)

### entity.spl — struct Entity
| method | mutates? | new form |
|---|---|---|
| is_null(self) | no | `fn is_null()` |
| eq(self, other) | no | `fn eq(other: Entity)` |

### entity.spl — struct EntityAllocator
| method | mutates? | new form |
|---|---|---|
| alloc(self) | YES free_head/generations/live_count | `me alloc()` |
| free(self, e) | YES generations/free_head/live_count | `me free(e)` |
| is_live(self, e) | no | `fn is_live(e)` |
| len(self) | no | `fn len()` |

### component_store.spl — ComponentStore<T>
| method | mutates? | new form |
|---|---|---|
| ensure_sparse_capacity(self, id) | YES sparse | `me` |
| contains(self, e) | no | `fn` |
| insert(self, e, value, tick) | YES dense/ents/ticks/sparse | `me` |
| remove(self, e) | YES dense/ents/ticks/sparse | `me` |
| get_slot(self, e) | no | `fn` |
| touch(self, e, tick) | YES ticks | `me` |
| len(self) | no | `fn` |
| entity_at(self, slot) | no | `fn` |
| tick_at(self, slot) | no | `fn` |

### change_detection.spl — ChangeTracker
| method | mutates? | new form |
|---|---|---|
| push_removed(self, e, tick) | YES removed | `me` |
| drain_removed(self) | YES removed = [] | `me` |
| is_changed_since(self, t) | no | `fn` |
| bookmark(self, tick) | YES last_seen_tick | `me` |

### system.spl — Scheduler
| method | mutates? | new form |
|---|---|---|
| add(self, name, run) | YES systems | `me` |
| disable(self, name) | YES systems[i].enabled | `me` |
| enable(self, name) | YES systems[i].enabled | `me` |
| step(self, ctx_ptr) | YES tick | `me` |
| now(self) | no | `fn` |

### world.spl — WorldBase
| method | mutates? | new form |
|---|---|---|
| spawn(self) | YES (via alloc.alloc()) | `me` |
| despawn(self, e) | YES (via alloc.free()) | `me` |
| is_live(self, e) | no | `fn` |
| advance(self) | YES tick | `me` |
| now(self) | no | `fn` |

### query.spl
Free functions only — no `self`, no change.

Totals: 16 mutating → `me`, 13 read-only → `fn` (self param dropped).

## Evidence — JIT-bail A/B (identical probe build/ecsme_probe/probe.spl)
BEFORE (`git show HEAD:` ECS restored):
  [INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
  cannot modify self in immutable fn method 'EntityAllocator.alloc'. ...
AFTER: 0 occurrences of "falling back to interpreter".

Probe output (identical BEFORE/AFTER, and identical under
SIMPLE_EXECUTION_MODE=interpreter vs default JIT):
  ids: 0,1,2        <- distinct entity ids (old symptom was all id:0)
  gens: 1,1,1
  tick: 2
  despawn_b: true live: 2   <- 2-hop mutation w.alloc.free() persists
  b_live: false a_live: true
  store_len: 2 / a_slot: 0 c_slot: 1

## Regression (all 0 failures)
ds, devfs, pipefs, procfs, rs, clock, sched service specs; container_manager;
tty_termios_ld; wm_world_multi_window_identity; mdsoc_plus_ecs_advisory.
`bin/simple lint` on all 5 changed files: "Lint passed: all files clean".

## PRE-EXISTING red (A/B proven, NOT a regression)
test/01_unit/lib/ecs/ecs_spec.spl — 6 failures, byte-identical set BEFORE and
AFTER: "semantic: method 'to_equal' not found on value of type i64/bool in
nested call context". Matcher/harness defect, unrelated to `me`.
