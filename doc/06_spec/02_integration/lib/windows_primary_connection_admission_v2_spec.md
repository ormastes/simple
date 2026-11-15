# Windows primary connection admission negative procedure

Status: **NOT_RUN; NATIVE FIXTURES UNAVAILABLE**. This is an authored procedure,
not an executable spec or a coverage claim. No tests or builds were executed.

The required Host journal foundation is **unlanded** in the separate
`/home/yoon/dev/simple-parallel-podman-ci-20261107` worktree. Its
`windows_journal_store_v1.spl` facade re-exports actual private-root classes;
it does not expose token constructors. The working bridge provides
`WindowsJournalStoreV1.belongs_to(root)` and
`WindowsJournalConsumptionV1.belongs_to(store)`. Until that dependency lands
and real enrolled Windows fixtures exist, all procedures below remain NOT_RUN.

Boundary under review:
`src/lib/nogc_sync_mut/io/windows_primary_connection_admission_v2.spl`.
Call the actual `windows_primary_connection_authorize_v2` and
`windows_primary_connection_claim_v2` APIs with retained native owners.

## Required native setup

Use an isolated, genuinely enrolled Windows deployment with its retained root,
current protected policy, actual journal, signed authority snapshot, executing
parent/helper chain, and valid budget proof. Use service-incarnation scope with
empty boot ID. Obtain stores only through the retained roots'
`open_journal_store_v1()` and consumption receipts through their actual
`publish_consumption(relative, payload)` path. Encode consumption metadata with
the production codec. No raw-token constructor, fabricated verified admission,
synthetic process owner, or hand-written native receipt substitutes for this
setup. Keep real policy/deadlines unchanged during each bounded observation.

## Unrelated private journal and wrong-root receipt

1. Retain enrolled deployment A and its actual journal/store A. Open a separate,
   legitimate private root B and its actual store B. Publish a canonical but
   unsigned connection consumption record in B and obtain native receipt B.
   Private storage and canonical encoding establish no execution signature.
2. Call `windows_primary_connection_authorize_v2` with deployment A, journal B,
   that record and receipt B. Require refusal with
   `windows-deployment-journal-owner-mismatch` from the deployment/store check
   and no verified capability.
3. In a separate fresh receipt case, pair journal A with receipt B. Require the
   `primary-connection-journal-origin-mismatch` from the receipt/store check
   before any one-use claim or Engine pipe acquisition.
4. Observe the real native claim/acquisition boundary using available native
   instrumentation. As an independent post-denial claim witness, claiming the
   rejected receipt's exact bytes once must still succeed. This diagnostic
   claim never produces a verified connection capability or permission for IO.

## Same actual root with unsigned execution proof

1. Use A's actual journal, genuine executing parent/helper chain and valid signed
   budget. Through supported retained-owner fixture publication, persist a
   canonical execution-proof record whose execution signature is absent or
   invalid. Keep packet, consumption and proof digests consistent so the
   signature verifier, rather than a digest mismatch, is the intended boundary.
2. Obtain a real consumption receipt from A and call the actual authorizer.
   Require execution signature verification to refuse, no verified capability,
   and no claim or Engine pipe acquisition. Record the actual propagated error.
3. Confirm the receipt remains unclaimed using a separate post-denial native
   claim observation. If supported protected publication refuses the negative
   fixture earlier, report that refusal and mark the signature-boundary case
   unavailable; do not count an earlier refusal as signature coverage.

## One-use claim replay

1. In a fresh actual-root case, use fully valid signed execution and budget
   proof to obtain a verified admission from the real authorizer. Retain a copy
   of that same opaque value; do not synthesize another receipt.
2. Call `windows_primary_connection_claim_v2` once and require a valid bounded
   window. Before expiry and without policy/journal changes, call it again on
   the retained copy. Require `primary-connection-consumption-not-claimed`.
3. Require no second successful claim and no second Engine acquisition. Claim
   testing itself need not open an Engine pipe. If expiry or authority changes
   intervene before replay, record the competing refusal and mark replay
   coverage inconclusive.

For every case retain actual operation ID, root/store provenance observations,
returned error, claim observations and pipe acquisition observations. Publish
neither keys nor raw native tokens. A successful storage write, valid SDN record
or ordinary consumption receipt must never be reported as verified admission.
