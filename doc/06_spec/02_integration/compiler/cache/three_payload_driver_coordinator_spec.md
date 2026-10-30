# Three-payload coordinator — exact inverse preparation

- Executable: `test/02_integration/compiler/cache/three_payload_driver_coordinator_spec.spl`
- Evidence class: authored executable SSpec definition; UNRUN.

## Scenarios

- Actual generation preparation reads two distinct named forward manifests and
  replaces one stale supplied RR shard with the exact declared-set inverse.
- All non-RR immutable objects and forward references remain byte-identical.
- Removing the final forward read produces no RR reference/object and leaves the
  earlier in-memory candidate fixture unchanged.
- Prepared-value reopening rejects missing inverse refs, extra stale RR objects,
  and a caller that removes the worker's forward ref together with its RR data.
- Missing, wrong-kind, digest-corrupt, omitted, incomplete, and conflicting
  forward evidence is refused.
- A valid prepared candidate still cannot cross the existing closed publication
  authority boundary; the named forward set does not prove global scope
  completeness.

## Required execution

After the source-pin owner qualifies the exact runtime, run once:

- `test/02_integration/compiler/cache/reverse_reference_coordinator_p5_spec.spl`
- `test/02_integration/compiler/cache/three_payload_driver_coordinator_spec.spl`
- `test/01_unit/compiler/cache/three_payload_generation_publication_transition_v1_spec.spl`

No execution receipt or concurrency/performance result is claimed here.
