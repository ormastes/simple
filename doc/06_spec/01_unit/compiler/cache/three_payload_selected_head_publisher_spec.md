# Selected-head publication preflight

Executable: `test/01_unit/compiler/cache/three_payload_selected_head_publisher_spec.spl`.
Requirements: REQ-CSM-007, REQ-CSM-008, REQ-CSM-009.

This authored companion covers logical validation of the integrated G3 durable
packet against G4's prior/target selected-head contract. The shared packet fixture
creates real canonical envelopes, journal frames and closure identities; its
copied durability fields do not establish physical host authority.

1. Bind a coherent target to its exact journal operation and closure. Preflight
   validates the packet, then returns `NamespaceUnavailable`.
2. Change prior revisions, generations and target identities. Validation refuses
   malformed or mismatched values before requesting any physical authority.
3. Change prefix bounds, prefix digests and operation digests. Each mismatch
   refuses the request.
4. Alter a copied durable sequence while preserving its operation digest. The
   journal owner detects that it does not name the selected record.
5. Append a later complete operation while preserving the admitted prefix.
   Logical validation accepts the original selected operation; publication stays
   closed pending the host namespace owner.

Execution and generated-manual qualification await the admitted self-hosted runtime.
The separate crash/restart system matrix remains pending implementation of its
physical issuer and recovery harness.
