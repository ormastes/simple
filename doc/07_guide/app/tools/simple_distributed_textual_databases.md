# Simple distributed textual databases: operator and developer guide

**Status:** Partial source implementation; runtime and deployment unverified

**Selected profile:** Authority A / Adapters A / Operating B / Retention A  
**Date:** 2026-10-03

This guide describes the intended operation of the SCV distributed textual
database and identifies implemented source entry points. Local command,
settlement, checkpoint and historical-query owners now exist in source, but no
admitted runtime has qualified them. The production GitHub/provider workflows
below remain requirements, not deployment receipts. This document does not
establish that a Git, CI, or issue-server round trip works today.

## Configured observation commands

The source command owner routes these commands through configuration and
reproduction admission, using an independently supplied policy digest:

```text
scv db observation-apply <policy-file> <policy-digest> <patch-file> <expected-head|empty> <external-evidence-parent>
scv db paged-observation-apply <paged-policy-file> <policy-digest> <patch-file> <expected-head> <external-evidence-parent>
```

The patch file contains the original signed typed patch; the command never
signs it or approves its metadata. Paged application requires an initialized
Paged store and the exact captured HEAD. Evidence storage must be outside the
checkout under the existing controlled-CAS scope rules. Ordinary `apply` and
`paged-apply` do not bypass the dedicated evidence owner.

Configuration/reproduction records bind exact content revisions. Declared
dependency availability must agree with observed content or retained evidence;
missing and restricted dependencies are explicit and do not establish
reproducibility. An accepted replay acknowledges the original immutable fact,
not current artifact availability. Reproduction commands are never executed by
admission. Responses identify the committed local HEAD, revision and replay
status; they are not protected remote settlement receipts.

Verification of declared CAS artifacts does not yet prove the complete mapping
from source and test-definition revisions to their reproduction artifacts.
That mapping and complete reproducibility remain open acceptance work, even
when every declared dependency is available.

Captured settled-alias dependency validation is covered by the Paged source
path. Reference command admission still lacks that alias-resolution path;
its current authored success cases use exact UID references. This is an open
compatibility gap, not a restriction of the selected requirement.

An available object with a verified missing or restricted transitive dependency
can receive an explicit incomplete-reproduction protection marker in the
retention catalog. Such a marker stops collection for the whole local catalog,
including resuming previously prepared deletions. It does not certify a complete
closure. Restoring bytes alone does not resume collection. The source now has
an explicit trusted local repair operation:

```text
scv db retention-status
scv db retention-repair-reproduction <expected-retention-head|empty> <external-evidence-parent>
```

Capture the retention HEAD with `retention-status` after restoring and registering
the required objects through their trusted storage owners. Repair reopens the
actual registered dependency graph under the SJ writer lease. Every marker must
retain its matching permanent reproduction pin. Missing, unregistered, corrupt
or restricted dependencies refuse repair and preserve all markers. Successful
repair removes only incomplete markers; ordinary pins, semantic state, catalog
classifications and deletion receipts remain unchanged. It performs no deletion.

`complete_closure_verified` reports a successful fresh check at repair time.
`no_incomplete_markers` reports an unchanged catalog without rechecking current
evidence. A stale captured HEAD requires a fresh status read. Repair is bounded
to 256 nodes, 8 MiB per object and 32 MiB aggregate encoded evidence reads;
catalog metadata reads are bounded separately. This source path still needs
runtime qualification and does not close the full reproduction or scale gates.

The interim observation/pin path inherits the existing retention owner's
256-object and 8 MiB per-object limits, with a 1 GiB aggregate content-read
reservation ceiling; bounded catalog metadata reads are separate. Command
patch input is bounded at 1 MiB. Larger dependency pinning and
Operating B qualification remain required work; these limits do not replace
the selected full feature requirements. The source command regressions must
execute on an admitted runner before this interface is qualified for use.

## What is being built

The design adds a local-first semantic database to SCV without adding an
always-on database server. Git establishes shared immutable bytes, jj manages
local revision work, and SCV validates typed semantic changes. GitHub is the
first planned live Git settlement and CI provider. Provider-neutral fixtures
also model GitLab CI, Jenkins-class, polling, event, and bundle-only sources;
passing a fixture will not by itself prove a live adapter exists.

The source repository and data repository are separate workspaces:

```text
simple/       source and normal development history
simple-data/  schema, identity, bugs, configurations, expectations,
              semantic batches, summaries, and evidence manifests
```

A sibling `simple-data` clone is preferred initially. The data repository has
one configured settlement remote and one protected `settled` ref. A local CI
worker, developer replica, or provider adapter may prepare changes offline,
but only the selected settlement authority may allocate compact numeric IDs.
Mirrors are read-only for allocation.

## Connection model

There are three distinct connections:

1. Git transport fetches canonical data and publishes a candidate commit with
   an expected old object ID. A non-force protected update or an admitted
   single-integrator equivalent serializes settlement.
2. A CI observation source discovers immutable run manifests and bounded
   evidence bundles through provider events, polling, or explicit bundle
   import. Webhooks are hints, never the durable queue.
3. A bug-provider bridge imports and exports provider-neutral semantic edits.
   GitHub issue numbers and future server IDs remain namespaced external
   bindings; they never become the SCV entity identity.

All local mutations pass through the existing SJ writer lease/capsule. Git,
jj, an IDE watcher, CI ingestion, and provider adapters must not independently
write the same checkout. Network calls occur outside the database write lease:
persist intent, release the lease, perform I/O, then reconcile through a new
controlled transaction.

GitHub is the first intended production adapter. Development before that
adapter exists should use deterministic contract fixtures for exact-head
fetch, stale-head rejection, uncertain publication, read-back verification,
event loss, overlapping polling windows, pagination, artifact expiry, and
provider permission loss. A test double is evidence of core behavior only.

## Identity and offline work

An offline replica creates an entity using the durable database namespace,
entity kind, a random actor incarnation of at least 128 bits, and a monotonic
actor-local counter. A cloned or rolled-back counter requires a new actor
incarnation. Existing SCV `ChangeIdentity` and `RevisionIdentity` values remain
canonical.

A developer workflow is intended to be:

1. Fetch or hydrate a known canonical checkpoint.
2. Create and edit typed changes locally under the SJ writer boundary.
3. Record an immutable `DbPatch` with its base, causal dependencies,
   preconditions, schema/reducer versions, signature, and stable batch ID.
4. Publish the batch to a discoverable inbox without claiming that its compact
   number is settled.
5. Fetch the accepted settlement receipt and replace provisional display
   references with their permanent aliases.

The settled alias is `(database namespace, authority epoch, entity kind,
u64)`. A table may display only the integer when a versioned header supplies
the omitted context. A copied bare integer has no safe meaning and must be
rejected. Accepted numbers are never reused, derived from row count, or
renumbered by compaction.

## Settlement workflow

The planned settlement worker performs this sequence:

1. Fetch canonical head `H`, the receipt chain, allocator high-water marks,
   aliases, accepted batches, and supported schema/reducer versions.
2. Authenticate and authorize the patch, then validate signatures, namespace
   and epoch, dependencies, preconditions, constraints, and reference closure.
3. Apply the pure reducer. Preserve real conflicts; remote arrival order does
   not manufacture causality.
4. Allocate aliases only after admission and build one candidate commit whose
   only parent is `H`. Allocator state, mappings, rewritten references,
   tombstones, and accepted-batch records change atomically in that tree.
5. Publish with the expected old object ID and without force.
6. Fetch and read back the accepted batch, commit, and signed hash-chained
   receipt before reporting numeric IDs as settled.

A stale head causes a complete replan from the new canonical head. An ambiguous
network result enters uncertain state and is checked against canonical history;
it must not allocate a second number. An ancestry, authority-epoch, or
high-water regression blocks further allocation.

## CI evidence workflow

At run start, freeze the source revision, test-definition revision,
configuration-set revision, and expectation revision. Workers record actual
observations locally and publish immutable bounded chunks plus a terminal run
manifest. An observation identity includes the source, provider instance, run,
job, attempt, test case, configuration, and payload digest dimensions declared
by that provider capability.

The privileged importer treats every bundle as untrusted data. It places bytes
in content-addressed quarantine outside the checkout; applies byte, file,
record, nesting, path, Unicode, decompression, and time quotas; rejects links
and device files; validates canonical digests; and never executes reproduction
content. Credentials available to the publisher must not be available to
untrusted build steps.

CI may append observations and evidence. It may not approve an expected
failure, close a bug, promote a custom configuration, or qualify untrusted fork
evidence for release. Missing chunks or a missing terminal manifest produce
`INCOMPLETE` or `NOT_RUN`, never PASS.

## Configuration-aware results

Observations, expectations, and evaluations are independent immutable facts:

- An observation records what happened for exact source, test-definition,
  effective configuration, case, run, and attempt revisions.
- An expectation revision records reviewed policy for a frozen configuration
  or configuration set.
- An evaluation classifies one observation against one named expectation
  revision as PASS, XFAIL, XPASS, signature mismatch, infrastructure error,
  NOT_RUN, INCOMPLETE, or UNCLASSIFIED.

Every custom-configuration failure must reference an exact `ConfigRevision`
and `ReproductionRevision`. The latter records immutable source or dirty-tree
bytes, typed arguments, fixture and input digests, seed, tool versions, device
state, artifact hashes, and availability. A local path or mutable jj change ID
alone is not reproducible evidence.

Operator summaries must show coverage separately from policy, for example
"12 pass, 1 known failure, 1 not run; 1 additional unclassified custom
failure." A later pass does not rewrite an older failure or prove other
configurations fixed.

## Bug and provider synchronization

A semantic edit and its canonical bridge intent are committed together. The
replica-local delivery lease and retry schedule are not canonical data.
Delivery progresses through `pending`, `leased`, `sent-unconfirmed`,
`acknowledged`, `conflicted`, or `quarantined`.

Adapters retain a namespaced provider binding, provider capabilities,
last-common state, causation identifiers, and read-back evidence. Independent
field changes may merge under schema policy; competing scalar changes remain a
conflict unless reviewed field authority decides them. Permission loss, a
filtered response, and deletion are distinct states. Following an uncertain
remote create, the bridge searches/read-backs its stable correlation marker
instead of blindly creating another issue or comment.

Periodic reconciliation is mandatory because provider events can be lost.
Cursors advance only after normalized input is durable and canonical acceptance
is recorded. Polling uses pagination and overlapping time windows with stable
deduplication identities.

## Retention and historical queries

Canonical Git retains semantic history: aliases, allocator state, settlement
receipts, bugs, configuration and expectation revisions, summaries, and
evidence manifests. Raw high-volume evidence belongs in a controlled external
content-addressed store (CAS), not permanent canonical Git ancestry.

Routine raw observations remain exactly retrievable for at least 28 days and
then may be represented by versioned daily cohort rollups. Unresolved failures,
release evidence, reproductions, and pending work pin their complete digest-
verified dependency closure until policy permits release. A manifest is not
proof that its bytes remain available.

Every historical query reports one resolution: `exact`, `aggregated`,
`restricted`, or `unavailable`. Counts deduplicate stable observation IDs.
Timing rollups use mergeable statistics or a documented sketch; daily
percentiles are not averaged. Late input creates a new rollup revision and
provenance.

Resnapshot data must preserve aliases, allocator high-water marks, tombstone
and merge knowledge, schema/reducer identity, accepted batches, and the history
catalog. Operations older than the supported replay horizon return
`ResnapshotRequired`; they are never heuristically replayed in a way that can
resurrect deleted entities.

## Proposed command surface

None of these commands is implemented merely because it appears here. Their
names and flags may change during implementation and CLI review.

```text
scv db status
scv db fetch
scv db sync
scv db publish
scv db settle
scv db resolve
scv db history --resolution exact|daily
scv db compact --dry-run

scv test config capture
scv test expectation set
scv test result record
scv test reproduce

scv bridge import
scv bridge export
scv bridge reconcile
scv bridge status
```

`publish` is intended to share only the database batch, not unrelated source
work. `settle` requires settlement authority. `reproduce` must hydrate and
verify dependencies before a separate, explicitly trusted execution step.
`compact --dry-run` must report exactly which evidence and query resolutions
would be lost before any destructive action is authorized.

## Failure states and troubleshooting

Until implementation exists, an absent command or adapter is expected; consult
the implementation plan rather than attempting operational recovery.

For a future implementation, diagnose failures without bypassing validation:

| Symptom | Meaning and safe response |
|---|---|
| `UnsupportedAuthorityCapability` | The remote cannot prove protected non-force compare-and-set/single-integrator publication and read-back. Disable allocator mode; do not fall back to force push. |
| `StaleHead` | Another settlement won. Fetch canonical state and replan the same batch; do not retain proposed numbers. |
| `PublicationUncertain` | The push may have succeeded. Fetch and search the accepted-batch registry and receipt chain before any retry. |
| `ReceiptRegression` | Ancestry, epoch, or allocator state moved backward. Fence the old authority and investigate restore history; use a new namespace if fencing cannot be proved. |
| `UnsupportedSchema` or `UnsupportedReducer` | Upgrade through a reviewed compatibility/migration path. Do not downgrade or guess at textual structure. |
| `BatchIdentityMismatch` | One batch ID has different canonical bytes. Quarantine it as corruption or identity collision. |
| `SemanticConflict` | Preserve both edits and resolve through a typed, attributed conflict-resolution patch. Do not hand-merge allocator files. |
| `QuotaExceeded` or malformed bundle | Keep the bundle quarantined, record provider/run provenance, and require a corrected bounded upload. |
| `IncompleteRun` | One or more declared chunks or terminal coverage evidence is missing. Reconcile the provider; do not infer PASS. |
| `ProviderEffectUncertain` | Read back by stable correlation/provider identity before retrying a create. |
| `ProviderAccessDenied` | Preserve the local entity and binding. Loss of visibility is not deletion. |
| `EvidenceRestricted` or `EvidenceUnavailable` | Report that resolution honestly; never substitute a rollup or manifest for exact bytes. |
| `ResnapshotRequired` | Hydrate the current checkpoint and semantically rebase supported pending patches; do not replay stale textual diffs directly. |
| SJ writer lease unavailable | Stop the mutation with a clear operational error. Do not start an independent Git, jj, or adapter writer. |

Never repair allocator state using row count or maximum live ID, force-update
the settled ref, discard aliases or tombstones to reduce size, execute an
imported reproduction during ingestion, or put credentials/secrets into Git
metadata. Incident and deletion reports must state that bytes already copied
into immutable Git history or other clones cannot be guaranteed erased.

## Performance and readiness

The selected Operating B target is one million aliases and one million retained
observations, with 10,000-observation imports. The latency, memory, recovery,
archive, and repository-size thresholds in the NFR are acceptance targets, not
measured performance. Phase 0 must first record reproducible baselines. Release
readiness requires three measured runs on the declared reference machine plus
fault-injection and live GitHub round-trip evidence; fixture-only tests are
insufficient for claiming the adapter operational.

## Design and evidence artifacts

- [Selected feature requirements](../../../02_requirements/feature/simple_distributed_textual_databases.md)
- [Selected non-functional requirements](../../../02_requirements/nfr/simple_distributed_textual_databases.md)
- [Architecture](../../../04_architecture/simple_distributed_textual_databases.md)
- [Detail design](../../../05_design/simple_distributed_textual_databases.md)
- [Configuration and reproduction admission checkpoint](../../../05_design/simple_distributed_textual_databases_reproduction_admission.md)
- [Paged historical regression design](../../../05_design/simple_distributed_textual_databases_paged_history_regressions.md)
- [Retention repair design](../../../05_design/simple_distributed_textual_databases_retention_repair.md)
- [System-test plan](../../../03_plan/sys_test/simple_distributed_textual_databases.md)
- [Parallel agent plan](../../../03_plan/agent_tasks/simple_distributed_textual_databases.md)
- [System-spec manual](../../../06_spec/03_system/app/scv/feature/simple_distributed_textual_databases_spec.md)
- [Local research](../../../01_research/local/simple_distributed_textual_databases.md)
- [Domain research](../../../01_research/domain/simple_distributed_textual_databases.md)
- [Original proposal](../../../01_research/app/tools/scv/simple_distributed_textual_databases_scv_jj_github_2026-09-13.md)

These artifacts define the selected design and its planned evidence. They do
not supersede implementation, verification, or release gates.
