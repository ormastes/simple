# ComponentRegistry attach count remains zero

Date: 2026-05-13
Status: Fixed (2026-05-19)
Severity: Engine component correctness bug

## Evidence

During async/GC engine component facade parity verification, the new facade
specs initially asserted canonical `ComponentRegistry.attach` behavior. The
same count failure reproduced in the existing canonical sync spec.

Command:

```bash
bin/simple test test/01_unit/lib/engine/component_registry_spec.spl --mode=interpreter
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

## Root Cause

`fn attach(self, node_id, component)` and `fn detach_all(self, node_id)` used
`self` as a positional value parameter. In Simple, this binds the receiver by
value, so mutations to `self.entries` inside the function body were silently
discarded. The read-only methods (`get_components`, `get_sprite`, etc.) correctly
used the implicit receiver (no `self` positional param) and worked fine.

## Fix

Changed both mutating methods in `ComponentRegistry` (2D) and `ComponentRegistry3D`
to use the `me fn` mutable-receiver form:

```
- fn attach(self, node_id: NodeId, component: Component2D):
+ me fn attach(node_id: NodeId, component: Component2D):

- fn detach_all(self, node_id: NodeId):
+ me fn detach_all(node_id: NodeId):
```

Files changed:
- `src/lib/nogc_sync_mut/engine/component/registry.spl`
- `src/lib/nogc_sync_mut/engine/component/registry3d.spl`

## Verification (2026-05-20)

Confirmed fix is present in both files:
- `registry.spl` line 118: `me fn attach(node_id: NodeId, component: Component2D):`
- `registry.spl` line 131: `me fn detach_all(node_id: NodeId):`
- `registry3d.spl` line 49: `me fn attach(node_id: NodeId, component: Component3D):`
- `registry3d.spl` line 58: `me fn detach_all(node_id: NodeId):`

Commit `efbbd6008a fix(ecs): resolve component registry attach count tracking` is in git log.
Status confirmed: Fixed.
