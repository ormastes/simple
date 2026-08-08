# JS Event Dispatch VM Growth

Status: OPEN production-performance blocker

Architecture and test planning (still RED):

- [`js_vm_reclamation.md`](../04_architecture/js_vm_reclamation.md)
- [`js_vm_reclamation_tldr.md`](../04_architecture/js_vm_reclamation_tldr.md)
- [`js_event_dispatch_vm_reclamation.md`](../03_plan/sys_test/js_event_dispatch_vm_reclamation.md)
- [`js_vm_reclamation.md`](../03_plan/agent_tasks/js_vm_reclamation.md)

## Symptom

Every JavaScript DOM-listener dispatch permanently grows interpreter state.
Long-running mouse, keyboard, timer, or animation workloads therefore increase
resident VM objects, functions, globals, and environments until navigation or
page close.

## Root cause

- `BrowserDomEventExecutor.ensure_event` allocates a host Event object, three
  native methods, and an append-only global binding per dispatch.
- Every callback invocation also allocates an `arguments` object and
  environment frame.
- `ObjectStore`, `EnvironmentStack`, native functions, and global bindings have
  no deletion, sweep, compaction, or free-list API.
- Callback environments remain stored, so a conservative escape scan always
  sees the Event parameter as reachable.

An Event-only reuse patch is unsafe: `lastEvent = event` must retain the old
object and identity after later dispatches.

## Required fix

Design one canonical JS VM reclamation owner for completed invocation
environments and unreachable objects/functions/globals. Prove closure captures
and escaped Event objects survive. Then share Event native methods and reclaim
only non-escaped transient Event material.

## Required evidence

1. A non-retaining listener dispatched 1,000 times keeps object, function,
   global-binding, property, and environment counts bounded after the first
   dispatch.
2. An escaped first Event remains distinct from a second Event and preserves
   its fields.
3. Captured callback locals and closures remain valid after their creating
   invocation returns.
4. Navigation and close reclaim the remaining page-owned VM state.

Do not close this report with counter filtering or Event-only reuse; both hide
the underlying append-only invocation leak.
