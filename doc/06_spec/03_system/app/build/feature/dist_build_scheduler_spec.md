# Distributed build parent owner — durable local evidence

**Status:** Manual draft for the executable [SSpec](../../../../../../test/03_system/app/build/feature/dist_build_scheduler_spec.spl). The current deployed pure-Simple runner cannot execute this new spec; no PASS or generated-manual check is claimed.

**Requirement covered here:** REQ-003, limited to durable local dependency admission, shared capacity across graphs, and stale-fence rejection after replay. This manual does not cover remote transport, real producer bytes, container execution, CI, hooks, signed GitHub reuse, or the selected numerical NFR.

## Operator flow

1. **Select exact source and policy snapshot.** Build canonical action identities from source, toolchain, environment and dependency manifests. The fixture uses distinct source names and immutable digests.
2. **Plan affected build and checks.** Open the parent owner journal. Confirm a consumer is unavailable until its producer is accepted. Reopen with prior accepted work and unrelated active work to check graph reuse and capacity.
3. **Dispatch admitted actions.** Admit attempts under the exclusive owner. An admission returns dispatch authority only after its journal record is durable.
4. **Validate and publish results.** Supply a parent-verified output manifest digest to the owner and accept only the current fence. Revoke a separate attempt before its delayed candidate arrives.
5. **Verify current integration candidate.** Close and reopen the journal. Inspect accepted action identity and attempt history; confirm a revoked candidate did not publish.

## Scenarios and expected evidence

| Scenario | Decisive assertion |
|---|---|
| Producer before consumer | Early consumer admission is rejected; producer publication is journaled; consumer admission then succeeds; replay retains both attempts. |
| New graph with prior history | An unrelated accepted action does not invalidate readiness. A concurrent active action still consumes global capacity: insufficient capacity rejects, sufficient capacity admits. |
| Revoked fence | Replayed owner refuses the late candidate with `scheduler-error: stale-fence`; accepted list remains empty. |

The fixture supplies an independently named manifest digest to the parent owner but does not materialize or verify artifact bytes. Its synthetic `lib.o` dependency shows accepted-action readiness; it is not dependency-byte provenance evidence. It proves the owner boundary, not a complete build. The later live two-node SSpec must run real compile/link actions, verify transferred bytes, exercise SSH/SFTP and Linux OCI recovery, and preserve the same fence decisions.
