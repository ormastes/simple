# Lane ECSGEN — ECS EntityAllocator generation fix

Status: DONE (not committed — lane is commit/push-forbidden)
Date: 2026-07-27
Bug: doc/08_tracking/bug/ecs_entity_generation_not_bumped_on_reuse_2026-07-27.md (OPEN -> FIXED)

## What changed

`EntityAllocator` stopped storing the free-list link inside `generations[]`.
Split into two arrays with one meaning each:

- `generations[id]` — generation only; bumped by `free`, never by `alloc`.
  Slot generations start at 1; 0 is reserved for `Entity.null()` and for
  `with_capacity` reservation padding.
- `next_free[id]` — link/state only: `-2` LIVE, `-3` RETIRED, `-4` RESERVED,
  `-1` free/end, `>=0` free with next-free index.

`is_live(e)` now requires BOTH slot state LIVE and generation match.

Wraparound policy: generations never wrap. At `gen_cap` (i32 max by default)
`free` retires the slot permanently (counted by `retired_slots()`) rather than
recycling it — a bounded id leak in exchange for "a generation is never
reissued". `with_generation_cap(cap)` lowers the cap so the policy is testable.

`ComponentStore` gained additive `get_slot_checked(e, alloc)` /
`contains_live(e, alloc)`. It was NOT made generation-strict because
`src/os/**` (out of lane scope) fabricates `Entity(id: n, generation: 0|1)`
handles for raw store lookups everywhere; making the raw path strict would have
broken every service.

Applied identically to all three trees:
`src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/ecs/{entity,component_store}.spl`
(`use std.ecs.*` resolves to `nogc_async_mut`).

## Files

- src/lib/nogc_async_mut/ecs/entity.spl
- src/lib/nogc_sync_mut/ecs/entity.spl
- src/lib/gc_async_mut/ecs/entity.spl
- src/lib/nogc_async_mut/ecs/component_store.spl
- src/lib/nogc_sync_mut/ecs/component_store.spl
- src/lib/gc_async_mut/ecs/component_store.spl
- test/01_unit/lib/ecs/ecs_spec.spl (5 new examples; existing ones untouched)
- doc/08_tracking/bug/ecs_entity_generation_not_bumped_on_reuse_2026-07-27.md

## Verdicts

- `bin/simple run test/01_unit/lib/ecs/ecs_spec.spl` — 8 / 4 / 2 / 1 / 1
  examples, 0 failures in every describe block.
- Same, `SIMPLE_EXECUTION_MODE=interpreter` — identical, 0 failures.
- Regression, all 0 failures:
  `test/01_unit/os/services/{ds,devfs,pipefs,procfs,rs,clock,sched}_service_spec.spl`,
  `.../container/container_manager_spec.spl`, `.../tty_termios_ld_spec.spl`,
  `.../wm/wm_world_multi_window_identity_spec.spl`.
- `bin/simple lint` on all changed .spl: 0 errors (warnings are the file's
  pre-existing SPIPE006/007 `expect(bool).to_equal(...)` style).

## Notes

- The binary used is the Rust bootstrap seed (`bin/simple` prints the seed
  warning banner), so these verdicts are seed verdicts.
- `with_capacity(n)` behaviour was deliberately preserved: the n padding slots
  are RESERVED, never allocated, so ids still start at n. Previously those
  padding slots reported `is_live(Entity(id: k, generation: 0)) == true` for
  k < n; that now correctly returns false. No `src/os/**` caller uses ECS
  `is_live`, so nothing depended on the old answer.

## Clobber incident (2026-07-27)

Mid-lane, a parallel session's working-copy sync reverted ALL of this lane's
edits (entity.spl x3, component_store.spl x3, ecs_spec.spl, the bug doc) back
to their pre-fix content while HEAD moved to 3721346d70a. Everything was
reapplied and fully re-verified afterwards; backups of the authored files now
live in /tmp/ecsgen/backup/ so a repeat is cheap to recover from. All verdicts
recorded above are from the RE-verification, on the post-clobber tree.
