# M2 Immutable Reverse-reference Projection Receipts

- Executable: `test/02_integration/compiler/cache/reverse_reference_projection_receipt_spec.spl`
- Requirements: `MBH-REQ-003`, `MBH-REQ-004`, `MBH-REQ-006`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- records exact facts through every typed registration API.
- persists every owner-published family through the BuildCache writer.
- does not report a consumer for a causally unrelated subject.
- distinguishes a published known-empty family from unknown state.
- keeps family boundaries separate.
- rejects a digest-valid receipt from an older cache generation.
- publishes canonical ordering independent of dependency input order.
- fails closed when the generation pointer is missing.
- rejects corrupt pointer schema instead of reusing entries.
- turns an immutable receipt mutation red.
- rejects an immutable-path collision instead of replacing bytes.
- turns dropping any authoritative family with a real dependent red.
- invalidates production cache admission after a causal provider mutation.
- proves boundary ordering schema and corruption behavior for every family.
- rejects a mismatched canonical source identity at exact-key lookup.
- rejects a valid synthesized replacement absent from the M2 receipt.
- binds M3 key frames to the exact immutable M2 publication.
- uses the production receipt reader to select the causal consumer.
- attributes a conservative closure rebuild when registry state is unknown.
- does not leak facts across sequential compilation owners or workspaces.
- keeps an ordinary `dependencies=[provider]` consumer reusable after a
  private-body edit while recompiling/emitting the provider and invalidating
  its proven relocation/link action;
- invalidates explicitly proven SCC peers after a private-body edit.
- follows exact semantic consumers after an exported-interface edit.
- computes the transitive causal closure through dependent consumers.
- reaches a stable SCC closure without dropping cycle members.

## Manual Steps
- Persist a real incremental build entry.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-03.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
