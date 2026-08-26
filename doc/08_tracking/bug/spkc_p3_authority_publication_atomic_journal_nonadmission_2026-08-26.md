# SPKC P3 authority-publication atomic journal is non-admitted

Status: OPEN (P1)

## Defect

The frozen P3 candidate is **NON-ADMITTED**. It does not yet prove the durable,
authority-safe atomic publication contract required after P2. P3 must not use a
publicly constructible lexical/state object as an authority substitute, nor
expose a partially staged publication through a convenience recovery path.

The only public ABI names for this slice are exactly:

- `stageAndPublishV1`
- `openPublishedAuthorityInventoryV1`
- `recoverAuthorityPublicationV1`

All authority constructors, record parsers, sealing helpers, journal paths, and
mutable current-pointer machinery remain lexical-private to the journal owner.
No additional public construction, reopen, or mutation API is permitted.

## Required P3 contract

`stageAndPublishV1` takes a P2-validated canonical input and stages its derived
objects privately. It writes immutable content-addressed objects, writes and
fsyncs a closed publication record, then advances the current pointer with a
durable compare-and-swap. A reader may expose a head only after the pointer,
record, and every referenced immutable object verify as one complete
publication. Recovery may finalize or discard interrupted private staging, but
may not invent a head or publish an incomplete record.

The closed record must rebind, from canonical bytes rather than defaults or
sanitization, at least its exact schema/version and field set, replay scope,
`publicationUid`, and the complete canonical input identity carried from P2.
An equal replay is not a cache hit until it also validates the persisted current
pointer and its referenced complete record/objects. A changed scope, revision,
expected publication identity, or canonical input must deny before pointer
advance.

## Fresh-session scope and evidence

Start a fresh lane from `42729de401ce624768227983e72c7a3dcec577c` with no
uncommitted source carried from the frozen candidate. The source lane owns only:

- `examples/05_stdlib/spipe/src/storage/authority_publication_journal.js`
- `examples/05_stdlib/spipe/src/core/knowledge_compiler_commit_publisher.js`
- `examples/05_stdlib/spipe/test/unit/authority_publication_journal_test.js`

`target_inventory_store_test.js` and every URI, cursor, projection,
materializer, MCP, and public-store surface are out of scope for this P3
repair. The frozen candidate changed only the three paths above; a fresh repair
must preserve that exact ownership boundary.

The test matrix is mandatory and must use real independent processes where it
claims restart or concurrent-reader behavior:

1. first publish creates only immutable objects, a closed record, and one
   durable current pointer; fault injection at every stage leaves readers on
   the old complete head or no head, never a partial head;
2. restart after each interrupted stage recovers only the prior complete head
   or the one complete new head;
3. concurrent readers during pointer advance each observe either the old
   complete publication or the new complete publication, never a mixed record,
   missing object, private staging path, or partially parsed input;
4. an equal replay validates the current pointer and referenced record/objects
   before returning idempotence; corrupt, absent, redirected, or mismatched
   pointer state is denied/recovered according to the closed journal contract;
5. altered record scope, `publicationUid`, schema/version, extra field, or
   canonical input bytes is rejected before projection or pointer advance.

Run the focused Node test once after the repair, then obtain an independent
highest-capability review of the exact three-file diff. Package/full-suite
results do not replace the restart and independent-process proofs. No source is
admitted or pushed until all five cases pass together and the review is PASS.

Cross-links: [W5A publisher gates](../../03_plan/sys_test/spipe_knowledge_compiler.md#224-ordered-remediation-gates-blocking-test-execution) and [remediation order](../../03_plan/agent_tasks/spipe_knowledge_compiler.md#wave-5-admission-remediation-execution-order-2026-08-26).
