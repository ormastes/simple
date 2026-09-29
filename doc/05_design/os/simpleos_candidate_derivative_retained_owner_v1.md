# SimpleOS candidate and derivative retained owner V1

Status: DESIGN ONLY; implementation and native evidence remain missing.
Reviewed base: `267b99c8c17` (2026-09-28). This elaborates producer 1 in
PR #1988, `simpleos_unified_release_verifier_next_2026-09-28.md`, whose report
is not present at this base. Authority: selected
`doc/02_requirements/feature/simple_platform_unification.md` REQ-017/018/019.
This document does not select new requirements or close a live release row.

## Concrete existing boundaries

| Existing owner | Reusable behavior | Missing behavior for this transaction |
|---|---|---|
| `src/os/installer/staged_root_tree_retained_provider_v1.spl` | Retained source descriptors, bounded positioned reads, identity validation | Writable derivative and frozen candidate storage; package boundary is installer; documented Linux provider |
| `src/os/installer/hosted_safe_artifact_io_v1.spl` | Private global redemption, no-follow root, atomic create-once publication | Disk lifetime after publication, positioned derivative writes, launch handoff; payload cap is 16 MiB |
| `src/app/io/composition_image_io.spl` | Owned copy of bytes read from a path | Retained file identity and immutable disk authority |
| `src/os/services/evidence/release_evidence_ledger_owner_v1.spl` | Serialized manifest consumption, live time, replay checks | Candidate acquisition, derivative creation, boot or persistence production |
| `src/lib/common/contracts/execution/simpleos_release_evidence_manifest_v1.spl` | Candidate and derived-state evidence value schemas | Authentication of the producing owner |

The hosted safe artifact native provider supports Linux and Darwin, but its
read closes the artifact descriptor before returning. Its retained root is
not a retained disk. A read descriptor alone also does not prevent another
writer from changing its inode. No QEMU retained-descriptor handoff was found
in the inspected `src/os`, `src/app`, or `scripts/qemu` paths.

## First implementation boundary

Implement a hosted preparation transaction that acquires actual bytes, freezes
an owner-created candidate object, creates a distinct writable full-copy raw
disk, and retains both until explicit close. It produces preparation evidence
only. Live QEMU, firmware admission, guest workflows and promotion remain
unavailable until their respective owners consume it.

Start with the Linux provider, with unsupported hosts returning a typed error.
Its candidate can use an anonymous file with enforced write/grow/shrink seals;
the derivative can use a distinct anonymous writable file under a retained
trusted directory. This is a proposed implementation, not a capability claimed
for current binaries. Implement orchestration, policy, hashing, lifecycle and
receipt encoding in Pure Simple. Add only the necessary descriptor/seal/process
boundary through the approved native-provider workflow, with a Pure Simple twin
and required shadow evidence. Darwin needs its own demonstrated freeze and
handoff mechanism before admission; permissions alone do not establish freezing.

The admitted candidate is the frozen object produced by this transaction.
The source import path is provenance, not an authority that survives import.
If an earlier release owner already admitted a candidate, import must redeem
that owner's retained authority and verify its actual object; an arbitrary
path cannot replace an already admitted candidate.

## Private authority and lifecycle

Proposed module: `src/os/services/evidence/candidate_derivative_owner_v1.spl`.
One private synchronized slot initially; concurrent prepare returns `OwnerBusy`.
The slot owns source, frozen candidate and derivative handles, byte counts,
computed hashes, lifecycle, generation and quarantine state. Public receipts
are bounded copied descriptions. Private grants contain generation/seal only;
every operation checks the live slot, so copying a grant cannot duplicate a
lifecycle or revive a consumed generation. Never return raw descriptors or a
public constructor for authority. Check generation exhaustion before I/O.

| Transition | Required behavior |
|---|---|
| Empty → Acquiring | Validate bounds, reserve identity, open source without following links, require a regular file |
| Acquiring → Frozen | Stream source into private candidate; detect truncation/short reads; enforce seals; hash the frozen object itself; close import source |
| Frozen → Prepared | Create distinct private derivative; copy from frozen candidate; sync; hash by retained readback; compare length and hash to candidate; retain both objects |
| Prepared → Leased | Future launch owner redeems one grant and receives controlled descriptor transfer; preparation API alone cannot enter this state |
| Leased → Prepared | Authenticated child exit and descriptor-return/revocation facts establish exclusive ownership again |
| Prepared → Finished | Hash derivative while quiescent, revalidate and hash frozen candidate; finalize a copied preparation receipt |
| Prepared/Finished → Closed | Consume all handles and invalidate generation exactly once |
| Any active state → Quarantined | Indeterminate sync, cleanup, close or child ownership; revoke further use; retain diagnostic facts |

Failure before publication must reclaim the reserved slot only after complete
cleanup. A consumed descriptor is never retried after ambiguous close. A stale
grant, foreign generation, repeated close or busy mutation fails without I/O.
Use bounded chunks (at most 1 MiB), checked byte-count arithmetic, explicit
maximum image bytes and disk capacity errors. Do not load disk images wholly
into heap. Timeout/cancellation must still run cleanup and record quarantine.

## Proposed API semantics

- `prepare_candidate_derivative_v1(source_authority, bounds)` acquires bytes;
  accepts no digest, immutable flag, state ID or guest-success flag.
- `candidate_derivative_snapshot_v1(grant)` returns copied preparation facts:
  owner-generated transaction identity, internally measured candidate SHA-256
  and length, derivative identity and initial digest, lifecycle, provider kind.
- `finish_candidate_derivative_v1(grant)` works only without a child lease,
  derives final digest and verifies candidate integrity from retained objects.
- `close_candidate_derivative_v1(grant)` consumes authority exactly once.
- A later package-private `lease_candidate_derivative_for_launch_v1` joins the
  retained launch owner. No public path or raw-handle launch escape exists.

An owner boot epoch is required if transaction identities escape the process.
Use provider-acquired entropy plus a monotonic generation; generation alone
repeats across restart. Hashes identify content and never replace capability
redemption. Crash recovery must reopen authenticated durable state or invalidate
all old transactions; this anonymous-file slice chooses invalidation.

## Evidence join and promotion

Keep preparation receipts separate from `SimpleOsReleaseEvidenceManifestV1`
until the production assembler can authenticate this owner's transaction.
`immutable_candidate` and `derived_only` can then be projected from successful
provider actions, never copied from callers. A full-copy raw derivative needs
an explicitly documented canonical representation for
`writable_overlay_digest`; do not invent a qcow2 overlay hash or use an unrelated
constant. Resolve this schema meaning before assembler integration.

The future launch owner binds admitted firmware and sealed plan authorities
before child creation, passes only the derivative as writable disk, and holds
that exact object across two distinct boot sessions. It must prevent reopening
a path after validation. Original candidate promotion later consumes the frozen
object from this owner after all live gates, never the mutated derivative or
the mutable import path. Durable promotion/export is beyond preparation.

## Required executable acceptance matrix

These are pending tests, not executed evidence. Put native integration tests in
`test/02_integration/os/services/evidence/` and SPipe scenarios in
`test/03_system/os/feature/`; mirror manuals under `doc/06_spec/` only.

| Case | Observable assertion |
|---|---|
| Import actual binary bytes including NUL | Independently computed digest and exact byte count equal frozen retained readback |
| Replace source path after prepare | Frozen candidate and derivative retain original imported bytes |
| Write/truncate frozen candidate through an alias | Provider rejects mutation; candidate digest remains unchanged |
| Mutate derivative through production write lease | Derivative digest changes; candidate bytes and digest do not |
| Distinct storage | Candidate and derivative identities differ; independent writes cannot affect candidate |
| Copy/stale/foreign grant | No additional authority, no I/O, no reopened closed generation |
| Invalid source | Symlink, nonregular, oversized, missing, truncated source fail without prepared receipt |
| Resource failure | Short write/read, no space, sync failure and identity failure clean up or quarantine |
| Lifecycle race | Two simultaneous preparations admit one; finish/close while leased fails |
| Native unsupported provider | Typed unsupported result and no prepared receipt |
| Restart | Prior process grants rejected; no recovered preparation assertion |
| Later QEMU integration | Cold boot uses leased derivative; reboot retains same state; candidate rehash unchanged |

Host preparation tests may prove filesystem behavior. They cannot prove NVFS,
SOSIX, guest compilation, authenticated version output or reboot persistence.
The existing six unified live verifier rows remain fail-closed.

## Ordered implementation checklist and handoff

1. Implement retained frozen-file and writable-file primitives with supported
   host identity, bounds, cleanup, sealing and failure injection evidence.
2. Implement the Pure Simple private transaction owner and the native acceptance
   cases above. Record admitted self-hosted runtime path, hash and provenance.
3. Add production image-owner redemption; prove already admitted candidates
   cannot be replaced by unrelated source bytes or caller-authored hashes.
4. Integrate launch-owner descriptor transfer and child lifecycle. Authenticate
   firmware/plan authorities and prohibit writable candidate inheritance.
5. Add persistence/guest producers, canonical full-copy derivative digest
   semantics, durable evidence assembler and unchanged-candidate promotion.

Merge owner: parent SimpleOS lane. Final reviewer: parent high-capability review.
This lane performed source inspection and document diff verification only. No
native primitive, executable test, owner implementation or live evidence was
added. The resource budget (about 1.9 GiB free at inspection) also precludes
assuming a complete image-copy/QEMU campaign can run in this worktree. This is
the explicitly requested design fallback, with production preparation still
`MissingEvidence` and REQ-017/018/019 completion unchanged.
