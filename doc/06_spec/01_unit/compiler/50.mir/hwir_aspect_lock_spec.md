# Content-addressed HWIR Aspect Locks

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl`

## Purpose and scope

This focused unit specification checks that a typed observational HWIR aspect
plan is bound to the exact `(id, version, content_hash)` manifest identity.
It also checks that a matching lock permits the declared module-port probe and
that an incomplete lock fails before an observational graph change can occur.

## Scenarios

1. Build a lock from the planned manifest, then detect a changed content hash.
2. Lower a small typed module and weave one locked observational output port.
3. Reject an empty lock for a plan that declares a manifest.

## Requirement traceability

- REQ-FV2-011 — the exact join-point application and weave identity enter the
  closure.
- REQ-FV2-019 — hash drift and an incomplete lock fail closed.

## Evidence boundary

This is typed unit-level plan/lock and probe-attachment evidence. It does not
qualify a dynamic aspect executor, establish a proof closure, emit or simulate
RTL, or prove that an RVFI observation validates HWIR or synthesized hardware.
