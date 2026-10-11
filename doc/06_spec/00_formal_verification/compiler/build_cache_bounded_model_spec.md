# Bounded production transitions and weighted work

Executable: [build_cache_bounded_model_spec.spl](../../../../test/00_formal_verification/compiler/build_cache_bounded_model_spec.spl).

Status: bounded Phase 1 execution passed in the final service cycle; SPipe/docgen admission remains
pending. This is finite-domain checking, not a universal theorem or measured
hardware performance claim.

1. Enumerate all 192 combinations of owner, lease identity/generation, result
   action, snapshot, success and cancellation. Call the real completion owner.
   Unauthorized inputs preserve the current lease; only an authorized coherent
   success publishes an artifact.
2. Enumerate all 625 four-event traces over two claimers, two completers and
   cancellation. Call the production service each time. Count actual execution
   authorizations and publication transitions; each remains at most one.
3. Reapply 16 claims while the current lease never completes. The actual service
   retains the dead owner's generation. This exposes its missing reclaim API;
   it is not a successful liveness check.
4. Enumerate 512 bounded weighted cold/warm work configurations. Account for
   capture, enumeration, hashes, reads, header decode, parse/HIR/MIR work,
   objects, links, startup, scheduler and receipt work. A doubled parse and a
   per-target scan have explicit additional cost; warm admitted reuse still
   pays decode/startup/scheduling cost. No count is called milliseconds.

The trace checker observes production service transitions. The weighted counts
are a proposed accounting model, not instrumented compiler work. A successful
bounded run cannot promote `FormalStatus` to `ModelProven`, `SourceRefined` or
`ArtifactVerified`.

Evidence/report: [formal verification report](../../../09_report/build_cache_formal_verification_2026-10-10.md).
