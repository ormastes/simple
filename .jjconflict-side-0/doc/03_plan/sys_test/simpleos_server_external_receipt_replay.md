# SimpleOS server external receipt replay continuation plan

## Scope

Continue `simpleos-server-executables` without weakening its current
fail-closed quarantine. The goal is a reviewer-authenticated, immutable,
three-architecture replay contract for `x86_64`, `arm64`, and `riscv64`.
This plan does not promote the TODO row and does not treat signed booleans as
semantic evidence.

Traceability: REQ-MCT-003 and REQ-MCT-005.

## Frozen interfaces

Production owners:

- `scripts/check/check-external-must-check-receipt.shs`
- `scripts/check/check-simpleos-filesystem-servers-qemu.shs`

Acceptance spec:

- `test/03_system/check/simpleos_server_external_receipt_replay_spec.spl`

Manual steps:

- `Authenticate the outer reviewer before loading bundle attachments`
- `Resolve each signed producer path to one immutable HEAD blob`
- `Replay retained HTTP database shutdown and fallback evidence`
- `Reject incomplete or aliased bundle evidence`

Checker helpers remain explicit failing placeholders until implemented:

- `accept_valid_three_architecture_bundle`
- `reject_untrusted_or_malformed_bundle`
- `reject_aliased_or_unsafe_bundle_paths`
- `reject_unreplayed_semantic_claims`

## Implementation sequence

1. Keep `simpleos-server-executables` in the semantic-validator-not-implemented
   quarantine while changing schemas and tests.
2. Define a versioned outer bundle with exact field allowlists and cardinality.
   Bind exactly one provisioned trust policy/key, three receipt/signature pairs,
   and seven artifacts per architecture.
3. Reject noncanonical repository paths and duplicate path or Git blob identity
   before materialization. Retain canonical-path and inode checks afterward as
   defense in depth.
4. Preserve signed `SimpleOsServerExecutionReceiptV1` bytes. Never open its
   producer-time absolute paths; resolve each signed role/path/hash to the
   reviewer-bound immutable HEAD attachment.
5. Retain and replay evidence that independently proves HTTP file behavior,
   database commit/reboot/read, shutdown, and no host fallback. A signed boolean
   alone cannot satisfy an acceptance ID.
6. Add table-driven mutations for missing, duplicate, extra, swapped, forged,
   aliased, noncanonical, tampered, legacy-v1, and unreplayed semantic claims.
7. Run the focused shell fixture and this modern SSpec once with an admitted
   pure-Simple runtime. Regenerate the manual with zero stubs.
8. Remove only this gate from quarantine after independent review accepts the
   full mutation matrix. Keep the ledger TODO until a real committed
   three-architecture production receipt passes.

## Acceptance boundary

The source implementation is ready only when all four SSpec scenarios pass and
docgen reports zero stubs. The outcome gate remains TODO until real
three-architecture evidence is admitted; fixture success cannot promote it.

## Handoff

Merge owner: must-check maintainer. Runtime evidence owner: SimpleOS platform
team. Final reviewer: an independent reviewer who did not produce or sign the
evidence. The rejected uncommitted prototype is diagnostic input, not an
accepted implementation.
