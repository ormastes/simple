# L7 semantic scope live owner V2

## Scope

This unit spec exercises only concrete owner operations that need no fabricated
semantic issuer, direct-reader pin, prepared payload, descriptor, or host
receipt. It deliberately does not construct opaque scope, grant, worker, or
verified-result handles.

## Scenarios

1. A copied reference to the same `SemanticScopeLiveOwnerV2` closes that one
   retained lifecycle. The original reference is then stale and returns the
   exact `AuthorityUnavailable` fallback.
2. Two owners created independently keep separate retained lifecycles: closing
   one does not close, recreate, or otherwise mutate the other.
3. The owner publishes its fixed limits: five issuer dimensions, 64 attempts,
   1,024 retained body objects, 65,536 dependency edges, and 128 MiB retained
   bytes.
4. The source boundary provides a prospective receipt/handle installation seam,
   but explicitly rejects projections whose gateway availability is false. The
   current issuer probes always return false, so no row can yet be installed.

## Deliberate exclusions

`begin_scope_v2` requires real writer, manifest, pin, closure, durable,
prepared-payload, and host authority receipts plus the complete sorted source
universe. `seal_scope_v2` additionally requires five installed live issuer
receipts. This focused owner spec does not fabricate those prerequisites; the
issuer adapter spec exercises owner mutation and receipt revocation, while the
worker integration owner must eventually supply the canonical admitted fixture
and authentic owner-completion leases. No copied DTO or test-created aggregate
substitutes for those authorities. This manual is handwritten and ungenerated;
runtime, docgen, and coverage remain unqualified.
