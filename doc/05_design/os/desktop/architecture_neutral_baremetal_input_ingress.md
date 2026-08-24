<!-- codex-architecture -->
# Architecture-neutral baremetal WM input ingress

## Decision

`DesktopShell` owns WM orchestration, not hardware selection. Its baremetal
loop retains one opaque scalar handle into a bounded ingress registry, polls
one event through the registered producer callback, then
stages and commits the compositor copy only when a concrete event exists.
An empty backend poll leaves the scene untouched and avoids the deep aggregate
copy that exhausts the freestanding bump heap.

An explicit x86 composition capability enables the temporary compatibility
path for the x86 entry that does not yet install `Ps2InputBackend`. Consequently,
the shell contains no port I/O and the same loop can consume PS/2, ARM64 VirtIO-MMIO, RV64
VirtIO-PCI, USB, or hosted input selected by the architecture composition root.

## Interfaces

- `DesktopShell.baremetal_input_handle` is the only retained boundary value.
- `baremetal_input_ingress_poll(handle)` resolves the bounded callback slot and
  returns at most one immutable
  `HostInputEvent` for owner-side commit.
- `Compositor.apply_polled_input_backend_event(event)` applies exactly one
  event, preserving the single pending WM pointer/key slot invariant.
- `DesktopShell.install_legacy_baremetal_readiness(callback)` receives a
  function capability only from the x86 composition root. Common/ARM/RV
  closures do not import the i8042 provider.

## Ownership and performance

The architecture callback's module owns mutable decoder and producer state;
the shell stores no optional trait/class alias or function value. The bounded
registry never reuses or releases a slot during the boot session, so a positive
handle cannot alias a later producer. The
compositor owns the event queue and scene. `HostInputEvent` crosses the boundary
as a value copy. `DesktopShell` commits the mutated compositor once after
polling succeeds. Idle backend polling performs no scene copy, tree scan, or
queue growth. One event is applied per loop iteration so later events cannot
overwrite the compositor's single pending action slots before the shell drains
them.

## Follow-up

The x86 composition root may install `Ps2InputBackend` and retire the legacy
compatibility methods after its mouse packet/coalescing evidence is preserved.
That migration does not change `DesktopShell`.
