# SPKC P3 authority-publication atomic journal is non-admitted

Status: OPEN (P1)

## Defect

The frozen P3 candidate is **NON-ADMITTED**. It does not yet prove the durable,
authority-safe atomic publication contract required after P2. P3 must not use a
publicly constructible lexical/state object as an authority substitute, nor
expose a partially staged publication through a convenience recovery path.

Four admission blockers remain after the earlier sealed-record, old-to-new head,
pointer revalidation, and open-reader findings were repaired in the candidate:

1. The authority bridge is duck-typed/forgeable. A caller can currently choose
   a journal root, replay scope, or canonical input instead of presenting one
   closure-branded authority bridge minted by the P2 publisher. That makes
   `stageAndPublishV1` an arbitrary-root/scope/input writer rather than the
   P2-to-P3 continuation. The bridge must be lexical-private and closure
   branded; all public arguments that purport to select those values must be
   rejected. P3 derives the root, replay scope, expected publication identity,
   and canonical input only from the sealed bridge after exact brand validation.
2. The current-pointer CAS lock is not yet a durable ownership protocol. It
   needs an fsynced owner receipt, a compare-and-remove/reclaim operation tied
   to the exact observed lock and receipt identity, stale recovery that cannot
   delete a replacement owner, and restart proof after the owning process is
   killed. Time-based path unlinking, a PID check alone, or a mutable caller
   supplied lock record is insufficient.
3. Competing stale-lock continuers can still turn a benign handoff into a
   thrown recovery failure. After a continuer has validated a stale lock but
   before it unlinks it, another valid continuer may remove that exact lock.
   That post-validation `ENOENT` is a lost-race result, not an error: the
   first continuer must re-read current state and return completed/retry. The
   same rule applies when the first continuer wins the `.retiring -> .done`
   claim rename: any follower observing `ENOENT`, the already-completed
   `.done` receipt, or a changed claim identity must idempotently return
   completed/retry, never throw or delete a successor claim. This continuation
   race leaves P3 non-admitted even when recovery authority remains fixed.
4. An orphan-claim cleaner can suffer an ABA path race. Two cleaners may
   observe the same stale claim path; after one retires/removes it, a recreator
   may install a new claim at that same path before the delayed cleaner acts.
   A path-only unlink can then delete the new claim. Cleanup must instead
   perform an exact-observed-claim identity transition (for example,
   compare-and-rename into a private quarantine name bound to the observed
   receipt identity), then revalidate that quarantined identity before removal.
   `ENOENT`, a changed identity, or a recreated path is a lost race and must
   return retry/completed without deleting any successor. This ABA condition is
   separate from ordinary stale-continuation idempotence and keeps P3
   non-admitted.

The only public ABI names for this slice are exactly:

- `stageAndPublishV1`
- `openPublishedAuthorityInventoryV1`
- `recoverAuthorityPublicationV1`

All authority constructors, bridge brands, record parsers, sealing helpers,
journal paths, lock-owner receipts, and mutable current-pointer machinery
remain lexical-private to the journal owner. No additional public construction,
reopen, or mutation API is permitted.

## Required P3 contract

`stageAndPublishV1` accepts only a closure-branded P2 authority bridge and
stages its derived objects privately. It writes immutable content-addressed
objects, writes and fsyncs a closed publication record, then advances the
current pointer with a durable compare-and-swap protected by an owner-receipt
lock. A reader may expose a head only after the pointer, record, and every
referenced immutable object verify as one complete publication. Recovery may
finalize or discard interrupted private staging, but may not invent a head or
publish an incomplete record.

The owner receipt is created durably before its lock becomes visible and binds
at least a fresh owner nonce, process identity, lock generation, and the
expected old/current-pointer identity. A reclaimer must re-read and compare the
same receipt and lock identity immediately before it removes either path; if
either changed, it loses the race and retries without deletion. The current
pointer update is authorized only while that exact owner receipt remains live.

Orphan cleanup is an ownership transition, never a path cleanup. A cleaner
captures the complete observed claim identity (at least receipt digest/nonce,
generation, and stable filesystem identity where available), atomically moves
only that exact claim into a cleaner-private quarantine/retiring name, and
revalidates the moved receipt before deletion. It must not unlink the public
claim path after its initial observation. If another cleaner has already moved
or completed the observed claim, or if a recreator has installed a different
claim at the original path, the delayed cleaner loses and reloads state; it
cannot infer permission to remove the replacement. The quarantine and its
parent-directory transitions are durable under the same journal fsync policy.

Recovery is a retrying, idempotent state machine. Following successful stale
receipt/lock validation, `unlink(lock)` may report `ENOENT` only because a peer
already completed that exact retirement; the caller then reloads the pointer,
lock, owner receipt, and retirement state and returns `completed` when the
desired head is already durable or retries from the new identity otherwise.
It must not throw solely for that race. A claimant moves only its exact,
revalidated `.retiring` receipt to `.done`; a loser that sees post-validation
`ENOENT`, a valid `.done`, or a changed receipt identity likewise reloads and
returns completed/retry. No continuation may unlink, rename, or infer success
from a path that it did not revalidate as its own exact claim.

The closed record must rebind, from canonical bytes rather than defaults or
sanitization, at least its exact schema/version and field set, replay scope,
`publicationUid`, and the complete canonical input identity carried from P2.
An equal replay is not a cache hit until it also validates the persisted current
pointer and its referenced complete record/objects. A changed scope, revision,
expected publication identity, or canonical input must deny before pointer
advance.

## Retained non-admission context

The repaired findings remain release-blocking context rather than being erased:

- prepared input must not be forgeable;
- persisted pointer and record bytes must validate the old-to-new head relation
  before an idempotent replay or recovery result is returned;
- pointer compare-and-swap must have a no-TOCTOU durability argument; and
- restart and concurrent-reader claims require independent-process evidence.

The bridge and lock requirements above strengthen these gates; they do not
relax the closed-record, object-completeness, or old-or-new-only contract.

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

1. a caller cannot construct, clone, serialize/reopen, or duck-type an
   authority bridge, and cannot select another root, replay scope, expected
   publication identity, or canonical input through the public P3 ABI;
2. first publish creates only immutable objects, a closed record, and one
   durable current pointer; fault injection at every stage leaves readers on
   the old complete head or no head, never a partial head;
3. restart after each interrupted stage recovers only the prior complete head
   or the one complete new head;
4. concurrent readers during pointer advance each observe either the old
   complete publication or the new complete publication, never a mixed record,
   missing object, private staging path, or partially parsed input;
5. an equal replay validates the current pointer and referenced record/objects
   before returning idempotence; corrupt, absent, redirected, or mismatched
   pointer state is denied/recovered according to the closed journal contract;
6. altered record scope, `publicationUid`, schema/version, extra field, or
   canonical input bytes is rejected before projection or pointer advance.
7. two independent publisher processes contend for a current-pointer CAS:
   only the exact owner receipt holder may advance it; a stale reclaimer cannot
   delete a replacement receipt/lock; and a SIGKILL owner is reclaimed only
   after a fresh process verifies stale receipt identity and restart safety.
8. deterministic independent-process barriers pause two stale continuers (a)
   after stale validation and before lock unlink, and (b) after claim validation
   and before `.retiring -> .done` rename. In each ordering, the loser sees
   `ENOENT`, a valid `.done`, or a changed exact identity and returns
   completed/retry; it never throws, removes the winner's successor, or exposes
   an incomplete head.
9. a deterministic independent-process two-cleaner/recreator barrier pauses
   both cleaners after they observe the same orphan claim and before either
   exact-identity retirement. One cleaner may win; before the delayed cleaner
   resumes, a recreator installs a different claim at the original path. The
   delayed cleaner must observe its stale identity/`ENOENT`/quarantined winner,
   return completed or retry, and never unlink, rename, or otherwise mutate the
   recreated claim. The test verifies the recreated receipt and claim remain
   readable and authority-valid after both cleaners finish.

Run the focused Node test once after the repair, then obtain an independent
highest-capability review of the exact three-file diff. Package/full-suite
results do not replace the restart and independent-process proofs. No source is
admitted or pushed until all nine cases pass together and the review is PASS.

Cross-links: [W5A publisher gates](../../03_plan/sys_test/spipe_knowledge_compiler.md#224-ordered-remediation-gates-blocking-test-execution) and [remediation order](../../03_plan/agent_tasks/spipe_knowledge_compiler.md#wave-5-admission-remediation-execution-order-2026-08-26).
