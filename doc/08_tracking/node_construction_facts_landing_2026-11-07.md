# Node construction facts: scoped landing

Date: 2026-11-07
Status: source review approved for the implementation and tests; runtime verification pending.

## Delivered scope

`src/compiler/00.common/data/node_lifecycle_contracts.spl` provides value-level construction facts over the canonical V1 data-schema surface. It validates schema identity and digest, selected-view applicability, canonical attribute IDs, and initialization bitmap shape. Transitions record initialization, completion, or explicit discard; unsuccessful transitions retain the supplied facts.

Completion requires an initialization record for every stored attribute applicable to the selected view. A declared default or optional field does not itself count as an executed initializer. Pending facts produce a scope-exit diagnostic, while resolved facts reject further initialization, completion, and discard transitions.

The accompanying `test/01_unit/compiler/data/node_lifecycle_contracts_spec.spl` contains 11 authored tests covering retained failure state, explicit default commits, duplicate initialization, pending/discard transitions, schema mismatch, invalid IDs and views, digest/version validation, empty surfaces, view applicability, explicit optional initialization, and malformed identities/bitmaps.

## Scope boundary

These functions describe construction facts. They do not allocate storage, execute initializer or cleanup code, publish nodes, validate topology, retire resources, or enforce compiler must-resolve behavior. Storage owners must perform their actual value operations before recording the corresponding transitions. The V1 surface cannot represent fieldless views or computed-property initialization policy.

## Evidence and pending verification

Astra reviewed the scoped implementation and its test source for this facts-only landing. The approved implementation blob is `8c3c2ff67224801cf3f4980a7891e93ecf2b5c14`; the approved test blob is `66157ad38d0373f94590a735fd1469c627c15e17`.

The 11 tests are authored but UNEXECUTED in this session because an admitted self-hosted compiler is unavailable. Runtime behavior and integration remain unverified; no verify PASS, allocation/builder completion, or cleanup-enforcement completion is claimed. The user authorized this source-complete scoped landing with runtime verification pending.
