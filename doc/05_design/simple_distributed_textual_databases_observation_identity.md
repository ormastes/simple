# Capability-pinned observation identity

Status: pure kernel, persistence codecs and twenty-two unit scenarios implemented in source; effect integration remains open. No runtime or requirement PASS.
Scope: selected REQ-017 and its REQ-024 capability boundary, with the original
Operating B targets unchanged. The existing effect-owner defect remains open.

## Pure contract

Reuse `DbCiCapabilities`; do not create a second provider-capability vocabulary.
`DbObservationIdentityPolicy` binds revision, database namespace, epoch, provider
instance, project and capabilities. Its independently supplied expected revision
must match recomputed canonical bytes. A matching digest is not authorization:
the effect owner must obtain that pin from admitted configuration.

Capability identity dimensions include the built-in instance, project, run, job
and attempt fields. Observation `provider.dimensions` contains only extra fields.
Subtract built-ins to derive the exact allowed extras; never derive declarations
from incoming data. Lists must be sorted and unique, and new-policy inputs reject
non-NFC spelling or reserved-name shadows. A provider emitting multiple cases per
job must declare its case/observation discriminator in the uniqueness tuple.
The kernel does not infer that discriminator or silently insert a case reference.

The identity key binds namespace, epoch, pinned policy revision, provider scope
and the declared uniqueness names/values. The content digest excludes only the
observation's own ingestion-assigned EntityRef and revision. Every other field,
including all provider dimensions, source/test/config/case/run/reproduction
references, actual outcome, failure signature, measurements and payload digest,
remains bound. The excluded reference must still be a valid sealed observation
reference of the correct kind and database context; nested config, test, case,
run and reproduction references must also match namespace/epoch where applicable.
Existing v1 wire and hash
domains must remain byte-for-byte unchanged; content comparison uses a new domain.

`DbObservationIdentityClaim` contains policy revision, identity/content digests
and the observation reference. It is a value, not a proof of trusted storage.
The decision function recomputes both claims from supplied original observations;
it does not accept an unverified caller-supplied content digest as equality proof.

| Input | Pure decision |
|---|---|
| Valid observation; verified index has no entry | Append |
| Same identity and content under a different own UID/revision | Duplicate(original reference) |
| Same identity; any other immutable content differs | Quarantine(QuarantinedIdentityReuse) |
| Existing lookup belongs to a different identity | Typed lookup error |
| Wrong pin, provider scope, namespace/epoch, declaration or quota | Typed error before a decision |

Limits are 64 names in each capability list, 64 observation dimensions and
measurements, and 4096 UTF-8 bytes per text value. Each observation has its own
1 MiB conservative canonical-work preflight; the inherited sealed-record codec
can impose a lower bound. A decision evaluates at most two such observations.
Policy encoding has separate fixed cardinality/text limits. These are not a
single 1 MiB whole-decision allocation or RSS budget. Validate counts and text
bounds before building the encoded body. No corpus-scale RSS or latency is
proved. Public helpers provide policy digest/seal, claim construction and
decision; no filesystem, provider process, signature authority or durable receipt
is implemented by this module.

## Required effect integration

Reference and Paged owners must bind a provider policy to the captured semantic
generation, read an authenticated identity-index entry and its original record,
compare the indexed claim to recomputed original content, then use the decision.
All ordinary apply, observation, settlement and checkpoint paths must enforce the
same invariant. A side file or a preflight scan outside the final CAS is insufficient.

Append publishes the observation and index atomically. Duplicate returns the
original immutable observation without allocating another identity or changing
its signed bytes. A mixed-operation batch cannot be silently rewritten to remove
duplicates; its exact signed-batch disposition must be defined by the effect
protocol. Quarantine preserves the rejected original signed input through
the existing controlled external quarantine owner, then publishes a durable
decision receipt without accepting the conflicting observation. Unknown or failed
quarantine publication must never be reported as a completed quarantine.
Prepare/recovery states, lease scope and exact commit ordering remain required
effect-design and implementation work; a pure Quarantine value is not that receipt.

Network/provider waits remain outside SJ. A losing semantic CAS reopens both
policy pin and identity index and recomputes the decision. Historical accepted
patch replay still reauthorizes under current trust; replay is not new cross-batch
provider deduplication. An identity-rejected candidate must not gain accepted-content
attribution. Existing conservative pins left by a losing CAS are not rolled back
speculatively; their retention/repair lifecycle remains authoritative.

The key deliberately includes the entire policy revision in this first version.
Even a transport-only capability change therefore requires an explicit migration
or a verified compatible upgrade protocol. An absent key under a newly supplied
policy must not reset deduplication. Existing unindexed observations need a
verified migration and collision report before indexed mode is admitted. Do not
silently relabel existing policy, keys or observations.

## Acceptance and performance obligations

Unit sources cover cross-UID duplicates, changed-content quarantine, distinct
attempts, non-unique dimension changes, declaration mismatch, malformed context,
wrong pins, canonical-name collisions and quota boundaries. Exact original v1
golden vectors remain compatibility gates. Unit decisions do not replace the
three REQ-017 system placeholders or the intended-failing filesystem regression.

Filesystem acceptance must cover both backends, exact rejected-wire readback,
recovery around every quarantine/index publication boundary, concurrent import
races, settlement bypass prevention, checkpoint index preservation and policy
migration. Existing `db_quarantine_import/open` provides controlled CAS mechanics;
its explicit bundle-import API alone does not implement automatic observation
quarantine.

Use a generation-bound indexed lookup, not a corpus scan on each request. Cache
only verified pages/policies under their generation/revision, invalidating on
HEAD, policy or epoch changes. The selected corpus remains one million retained
observations; warm dedup lookup p95 must be at most 250 ms, and validated import
of 10,000 observations at most 5 seconds and 256 MiB RSS. Measure p50/p95/p99,
startup and maximum RSS with the required fixture/machine receipts. No such
measurements or admitted-runtime test results exist for this module yet.

## Persistence contract

The persistence module encodes the entire policy and a compact index claim. Policy
wire uses `SCVDB-OBSERVATION-IDENTITY-POLICY-v1`, a single canonical positional
frame, lowercase hexadecimal and a final newline. It contains revision, namespace,
epoch, provider instance/project, both capability-name lists, all six capability
flags and the bundle bound. Decode must validate the independently supplied pin,
minimal framing, NFC, exact shape and complete re-encoding equality.

Index wire uses `SCVDB-OBSERVATION-IDENTITY-ENTRY-v1` and stores only policy,
identity and content digests plus the original structured observation reference.
It does not copy the potentially large observation body. Structural decode is
not verified lookup. Entry verification requires the expected identity digest,
pinned policy and an actual original sealed observation, recomputes the complete
claim and compares every field. Missing originals and mismatches are errors,
never an absent-index Append decision. The caller still owes authenticated
generation/page/row lookup; a self-consistent caller DTO is not that proof.

Wire limits are 2 MiB for policy and 32 KiB for an entry, enforced before hex
decoding. Child enumeration is bounded before allocation (14 policy fields,
64 capability names, four entry fields and two reference components). These
formats do not register a Paged record tag or upgrade backend import rules.
That requires a versioned index protocol and migration, still open.

## Mixed-batch equivalence and quarantine publication

Source inspection confirms the current identity map is bijective: two UIDs cannot
be assigned the same alias sequence. The existing file-identity correction log is
not database observation equivalence and must not be reused as its authority.
A full duplicate protocol therefore needs an immutable, versioned dedup link
from the newly proposed observation reference (including revision) to the original
reference, binding policy, identity/content digests and the original batch digest.

Derive any execution view from the authenticated original patch and verified
links; never reseal or rewrite the original wire. Lookup must reconcile incoming
and original reference revisions using the equivalence proof, not pretend they
are the same encoded reference. Typed references, nested references and preconditions
must resolve consistently through query, refcount, settlement and checkpoint
validation. Reject cycles, context/kind/content mismatches and collisions with an
already materialized incoming UID. Link, accepted/counter state, identity index
and the other operations must publish in one semantic CAS. A global constraint
failure aborts the entire batch. Until this exists, explicitly defer/reject the
whole duplicate mixed batch; silently skipping its duplicate operation is unsafe.
Such interim rejection is not completion of the idempotence requirement.

For quarantine, prepare and reopen the exact original signed bundle in controlled
external CAS before attempting decision publication. The direct-wire
`db_quarantine_store_bundle` operation accepts a canonical signed-bundle wire,
avoiding an extra temporary input file. File import retains its format, no-follow,
bounded read and UTF-8 checks, then delegates to the same operation. Canonical
bundle and signature-shape validation precede CAS mutation; signature shape is
not current authorization. The existing evidence CAS owner retains private
publication staging and its short SJ lease. Do not invoke this operation inside
an already held root lease. Under the final decision SJ/CAS, recheck semantic HEAD,
policy pin, identity index and original record. Publish a versioned decision
record binding batch/payload, rejected-object address and conflicting operations,
without accepting the batch/counter or applying any other operation. The decision
must share the versioned semantic image/page root; two channel commits are not an
atomic transaction merely because both hold SJ.

Crash before decision publication leaves an orphan CAS object, not success.
Recovery after publication must reopen the decision and exact bundle and
reestablish durability before returning a completed quarantine. A changed HEAD
requires recomputation; the prepared object grants no authority. Storage failure
cannot become a quarantine receipt. A durable decision may advance canonical HEAD
while accepted observations, counters, aliases and retention remain unchanged.
The current collision regression checks these accepted projections rather than
requiring a frozen HEAD; durable rejected-wire and recovery oracles are still
required before replacing its system placeholder.

### Prepared bytes are not a completed decision

The direct-wire storage handle contains CAS digest, exact wire digest, patch
count and caller-supplied accounting day. It proves no provider identity conflict,
policy admission or canonical acceptance. The day is not a signed creation time.
The owner stores `SCVDB-QUARANTINE-v1` plus the exact validated canonical bundle;
reopening checks object integrity and bundle identity. Repeating the same wire
and accounting inputs is idempotent under the existing content store.

Filesystem oracles must compare actual stored bytes and original patch signatures,
show direct/file import equivalence, distinguish signed shape from signature
authorization, reject malformed/over-quota wire before candidate storage, reject
checkout-internal destinations, and observe busy SJ refusal followed by retry.
Use populated accepted state when asserting no acceptance or retention mutation.
These tests establish storage preparation only; crash recovery of a canonical
quarantine decision, index fencing and mixed-batch atomicity remain separate gates.
