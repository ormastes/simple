# Atomic observation identity implementation plan

Baseline: `65f8e0173b8`. Status: researched implementation contract, unexecuted.
Scope remains REQ-001–036 and NFR-001–015 under the selected profile. This plan
orders the remaining REQ-017 work; it does not replace the broader acceptance plan.

## Why an observation-owner-only change is insufficient

| Existing boundary | Concrete coupling requiring a versioned change |
|---|---|
| `db_policy_codec.spl` | `DbPolicyConfig` and POLICY-v1 contain only admission and merge policy |
| `db_paged_model.spl` | Structure digest parses the POLICY-v1 reduction subtree by position; txn/index versions are fixed to v1 |
| `local_transition.spl` | LOCAL-v2 contains state and conflict catalog only; conflict resolution reconstructs the image |
| `checkpoint_reader.spl`, `checkpoint_store.spl` | Independently parse or emit LOCAL-v2; Reference checkpoint storage has only snapshot/identity/conflict fields |
| `settlement_remote_snapshot.spl` | Canonical remote projection has an exact three-file state/identity/settled shape |
| `db_paged_indexes.spl` and importer | Existing index tags 170–173 have closed validation; adding an unrecognized record is not an upgrade |
| `distributed_identity_map.spl` | UID/alias map is bijective and rejects duplicate sequences |
| `db_reproduction_exact` | Requested semantic revision must match; forwarding a duplicate UID alone breaks exact references |

The current pure kernel, codecs and quarantine byte store are dependencies,
not completed identity admission. A local-only index would be lost through
settlement or checkpoint import. An optional unpinned default would allow a
policy change to reset deduplication.

## State and version contract

1. A new policy version carries a canonical provider-scope map of sealed identity
   policies. Reject duplicate scopes and validate every independent pin. Bind the
   complete identity-policy set into generation structure. Ordinary signing-key
   or metadata rotation remains distinct from a provider identity-policy change.
   Order scopes by the tuple `(provider_instance, project)`, comparing the first
   component and then the second; delimiter-concatenated keys are ambiguous.
2. A new Reference local image carries a canonical identity catalog containing the
   policy-set revision, identity claims, dedup links and quarantine decisions.
   Include this catalog in the authoritative generation root, even when accepted
   rows and their materialized-state revision do not change.
3. A new Paged transaction/index version carries the same logical records with
   authenticated point lookups and a generation policy-set pin. Reserve numeric
   record tags only after checking all existing registries. No whole-store scan
   is permitted in the hot deduplication path.
4. Version Git projection, settlement receipts and checkpoint storage together.
   Readers validate index-to-original consistency, terminal dedup links, decision
   provenance and preserved accepted state. Historical version dispatch must be
   explicit; do not append ignored fields or silently reinterpret v1 bytes.
5. Fresh configured empty stores initialize indexed mode and accept valid
   observations normally. Existing unindexed stores require an explicit bounded,
   resumable migration: capture HEAD, validate all retained observations, build
   indexes, report collisions, preserve history, then install by expected-HEAD CAS.
   Legacy reads and authenticated exact accepted replay remain supported. A new
   policy-derived absent key is not evidence that old observations never existed.

## Duplicate semantics in mixed batches

There is one canonical observation per provider identity. Preserve the original
signed incoming record/batch as immutable provenance; do not count or expose a
second canonical observation merely to satisfy existing row lookup machinery.
A versioned link binds the proposed incoming reference and revision to the
original reference, policy, identity/content digests and original batch digest.
Retained signed provenance must be available to validate the link; an accepted
batch hash alone does not retain the signed patch.
Authoritative links and decisions must also protect their referenced signed
provenance from collection. Validate these dependencies against the captured
generation before deleting objects; this is distinct from attributing rejected
content as accepted and cannot be replaced by an independent side-channel pin.

Incoming and original revisions differ because the own UID participates in the
old record hash. Resolve that difference through a verified equivalence protocol,
not string substitution. Typed references, nested references, preconditions,
refcounts, aliases and historical lookup must agree. Reject cycles, chains where
a terminal original is required, foreign scope, changed content and collision
with an already materialized incoming UID. Apply unrelated operations and all
global constraints against the same resolved view; commit links, accepted batch,
actor counter, identity index and other changes in one CAS. Any constraint failure
aborts the entire batch. Never rewrite or reseal the original signed patch.

## One authority boundary across all paths

The transition input must carry full trusted configuration and captured catalog
or authenticated page proofs. Admission/merge-only legacy APIs cannot authorize
indexed observation mutation by themselves. Cover these callers together:

- Reference admitted and settled planning, allocation, local apply and conflict
  resolution, observation admission and mixed GitHub binding batches.
- Paged begin/advance planning, conflict intents, final transition, observation
  admission and mixed GitHub binding batches.
- Local and Paged settlement prepare/resume, uncertain-publication reconciliation
  and canonical Git snapshot readback.
- Checkpoint pending-patch preview, full import, monotonic preservation and install.
- Final promotion of quarantined input; authentication preparation alone is not
  final identity admission.

Keep existing generic reserved-kind guards. Do not substitute a blanket ban on
fresh observations for implementation of indexed admission.

## Quarantine decision and recovery

Prepare exact canonical signed-bundle bytes outside the final SJ lease using
`db_quarantine_store_bundle`, reopen them, then recheck generation, policy, index
and original at final publication. Commit a decision binding batch/payload,
prepared-object address and conflicting identities in the authoritative image
or page root. Do not accept the batch, consume its actor counter, apply unrelated
operations or attribute its content as accepted. A decision-only HEAD advance is
valid; a second channel write is not an atomic substitute.

Before-CAS crash leaves an orphan, not success. After-CAS recovery reopens the
decision and exact object and reestablishes durability. A losing CAS recomputes
against the winner. Tests must exercise a real interleaving between lookup and
publication through a trusted internal boundary or controlled hook. No finalizer
may accept a fabricated plan-shaped DTO as authority; tampered prepared inputs
must be rejected or independently re-derived.

## Acceptance sequence on both backends

| Scenario | Required reopened evidence |
|---|---|
| First indexed append | Policy pin, original observation, exact identity entry, accepted batch and counter in one generation |
| Same-content new UID plus another operation referencing it | One canonical observation, unchanged signed batch, committed unrelated work, valid equivalence and resolved reference |
| Same identity with changed failure signature | Exact rejected signed wire plus committed decision; unchanged accepted rows, counters and retention |
| Transport capability flag changes policy revision | Explicit migration/refusal; no absent-key append under a new policy |
| Two preparations race from one generation | Only one authoritative candidate; loser reopens and recomputes without mixed index/accepted state |
| Checkpoint/remote round trip | Policy set, indexes, links and decisions survive complete authenticated validation |
| Crash at each quarantine publication boundary | Correct orphan/recoverable/committed classification from actual durable objects |

Reuse `db_artifact_binding_fixture`, `db_provider_identity_fixture` and direct-wire
quarantine fixtures. Mixed-reference schema must be installed before Paged genesis.
Keep the existing collision regression intended-failing until the real owner is
fixed; do not replace system placeholders with pure-kernel assertions.

## Delivery ownership and stopping conditions

Root is interface/merge owner and final reviewer. On separate release-derived
worktrees, core owns versioned pure schemas/codecs and deterministic link planning;
research owns effect-path implementation after interface freeze; evidence owns
independent actual-owner acceptance fixtures. Reassign overlapping files explicitly
before edits. No lower-model sidecar is required for this coupled change (N/A).

Land no partial protocol upgrade. Integrate source in dependency order: schemas
and test-first fixtures; complete readers/import validators; transition owners;
settlement/checkpoint propagation; migration/recovery; then runtime qualification.
Run each unchanged acceptance check once, allow at most three repair cycles and
report unresolved failures. Required compiler/lib/MCP/LSP, core/native smoke,
coverage and Operating B evidence remain gates. Static review cannot provide
RED/GREEN results while the admitted runtime is unavailable. Finish still requires
the complete selected acceptance boundary and a reviewed merged PR.

## First schema dependency: POLICY-v2

`DbIdentityPolicyConfig` contains `revision`, the pinned v1 `base` configuration,
and a nonempty ordered `identities` list of at most 64 pinned provider policies.
The wire header is `SCVDB-POLICY-v2`; a canonical three-field list contains the
outer revision, exact canonical v1 base wire, and list of exact canonical provider
policy wires. The complete wire is bounded to 16 MiB before decoding. Every
identity namespace/epoch must match the base. Canonical decoding must reject
duplicate or out-of-order scopes, extra fields, nonminimal frames and trailing
bytes. Check aggregate encoding size incrementally, before building a full
oversized envelope.

The full configuration uses domain `policy-config-v2`; the separately computed
`identity-policy-set-v1` digest binds namespace, epoch and the complete canonical
scope map. A capability flag change changes both pins. Signing-key or metadata
rotation changes the full pin but not the identity-set pin. Public scope selection
validates the full configuration and refuses unknown scopes.

This schema does not activate indexed writes. Legacy readers reject its header;
callers must not discard the identity map and pass only `base` to bypass the
versioned transition requirement. Tests are authored before the implementation;
without the admitted runtime, their execution status remains UNEXECUTED.

Integrated source checkpoint: test commit `0657ee341a9` contains fourteen unit
cases; implementation commit `30ff166358e` adds the POLICY-v2 module. The initial
test source existed before implementation began. Root and the independent
reviewer checked the source contract; root reviewed the final aggregate encode
quota case. No runtime RED/GREEN, coverage, doctest, backend acceptance or release
PASS follows from this checkpoint. Next integration still requires the versioned
catalog, provenance records, complete readers and owner transitions above.
