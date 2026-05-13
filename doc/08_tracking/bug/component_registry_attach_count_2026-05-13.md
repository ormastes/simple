# ComponentRegistry attach count remains zero

Date: 2026-05-13
Status: Open
Severity: Engine component correctness bug

## Evidence

During async/GC engine component facade parity verification, the new facade
specs initially asserted canonical `ComponentRegistry.attach` behavior. The
same count failure reproduced in the existing canonical sync spec.

Command:

```bash
bin/simple test test/unit/lib/engine/component_registry_spec.spl --mode=interpreter
```

Observed result: 5 examples passed and 3 failed. The failing examples expected
attached components to be counted, but `get_components(...).len()` returned
`0` after `attach`.

## Impact

The new `std.nogc_async_mut.engine.component.*` and
`std.gc_async_mut.engine.component.*` facades can import and use component
records, enum helpers, mesh helpers, and camera/tilemap extensions. Full 2D
registry mutation behavior remains weak until the canonical registry failure is
fixed.

## Next Steps

- Debug `me attach` mutation persistence for `ComponentRegistry.entries`.
- Add an assertion that `get_sprite` / `get_camera` actually returns `Some`
  instead of relying on conditional assertions.
- Re-enable facade-level attach behavior coverage after the canonical sync
  registry spec passes.
