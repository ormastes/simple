# Engine2D: `engine2d_software_offscreen_dispatch_spec` asserts a software dispatch rung that does not exist

Status: OPEN (spec red since it landed; owner decision needed). Found
2026-11-15 on `work/engine2d-vulkan-text-20261115` (base `830879893c3`).

## What fails

`test/03_system/check/engine2d_software_offscreen_dispatch_spec.spl` is 0/3
at the base and after this lane's change. It is a source-text guard: it reads
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` and expects, in every
primitive / frame / readback method, an arm

```
elif val Some(software) = self.software_backend:
            software.<op>(...)
```

plus more than 24 `self.software_backend = Some(software)` /
`self.backend = software` write-backs.

## Why it is red

No such arm has ever existed on any ref: `git log --all -S
"software.draw_rect_filled(x, y, w, h, color)" -- .../engine.spl` finds
nothing. The spec's only commit is the 2026-09-29 transplant
`88aac2ffe28`. `engine.spl` itself records the opposite state as an open
item, TODO `[gpu][P2] No software/CPU dispatch rung exists` (todo rows 21 and
303 in `doc/08_tracking/todo/todo_db.sdn`): `software_backend` is read only
for compositing and shutdown, every software draw falls to `else
self.backend`, and the TODO forbids adding the rung "without re-proving the
hosted lane" because a 2026-07-16 attempt broke every `create_offscreen`
caller.

`test/01_unit/lib/gpu/engine2d/engine_software_lane_contract_spec.spl` pins
that current state ("There is no `elif val Some(sw) = self.software_backend`
arm in any primitive method"). The two specs contradict each other; one of
them must be red until the rung lands.

## Not done here, and why

- The spec is not wrong about the goal (the freestanding lane traps a trait
  call with no vtable), so it was not edited or skipped.
- Adding the rung needs the freestanding proof the TODO names (an
  `x86_64-unknown-none` build showing the trait call is gone), which needs a
  bootstrap. That is outside an engine2d lane.

Owner decision: either land the rung with that proof (then flip
`engine_software_lane_contract_spec`), or mark this system spec
`@tag:in-development` against todo 303 so it stops reading as a regression.
