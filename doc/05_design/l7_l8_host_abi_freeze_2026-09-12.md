<!-- codex-design -->
# L7/L8 descriptor authority and host ABI freeze

Date: 2026-09-12. Status: **DESIGN CANDIDATE; production activation NOT ADMITTED**.
Owner/planner: Astra; implementation: Sol; independent acceptance: Astra.
This is an additive interface decision within the already selected three-file
compile requirements, not a new requirement selection or a physical proof.

The [dependency manifest](l7_l8_host_abi_dependencies_2026-09-12.sdn) freezes
the exact common-contract bytes observed at design time. The
[agent plan](../03_plan/agent_tasks/l7_l8_host_abi_freeze_2026-09-12.md) freezes
ownership, test names and integration order. The existing authority-completion,
host-prerequisite, formal-audit and eight-scenario baselines are provenance
references pinned in that manifest, not candidate-local links or an assertion
that this docs-only commit contains those unadmitted source/doc dependencies.
Their contracts remain normative except for the explicit old/target-head and
outcome corrections here. D0 admission must supply them before dependent
implementation/acceptance; the self-contained ABI below can be reviewed first.

## 1. Admission and source boundary

Captured shared HEAD: `27cc9180546a54673e1df39f504782a412223b21`.
G integration reference: `3900ad78912ff18315109dba1bfbc9f7462125f2`.
Prior formal-doc candidate: `f6b21f5c7af5a89aa16533b7c82112de59d413a2`
(base `7352f99898cbc04ce3b367b383d90d34a18b44a4`).
These are independent provenance references, not an implied ancestry chain.
The manifest's 29 files are the complete observed `00.common/cache_contract`
directory, **not** a claim to include the transitive compiler/runtime closure.
Fifteen are absent from captured HEAD; fourteen are absent from G's base.
Four existing files have different working bytes. Each missing/changed blob
requires a source-owner commit and exact integration receipt before a dependent
compile can be called reproducible. A working-tree digest is not source admission.

No availability flag may become true from this document, a copied DTO, a
positive handle integer alone, a structural replay, or a matching digest.
Existing capped Lean results remain authored/unadmitted; no fourth proof run,
axiom audit, SSpec execution or power-loss PASS is introduced by this freeze.

The following existing owners are extended; do not add parallel journal, CAS,
GC, namespace, selected-head or semantic issuers, or new version-numbered files.

| Existing path (relative to repository) | Responsibility retained |
|---|---|
| `src/lib/common/cache_daemon_host_authority_v1.spl` | New V3 typed host wrappers and raw ABI declarations |
| `src/lib/common/cache_host_authority_v1.spl` | Existing root/object descriptors and reader-pin owner |
| `src/compiler/80.driver/cache/gateway/cooperative_namespace.spl` | Private namespace/scope admission and participant completeness |
| `src/compiler/80.driver/cache/gateway/cooperative_namespace_host_prerequisite_v1.spl` | Existing selected-head V1 codec, diagnostic inventory |
| `src/compiler/80.driver/cache/gateway/cooperative_namespace_gc_begin_authority_v1.spl` | Same-scope complete-root contribution admission |
| `src/compiler/80.driver/cache/publication/three_payload_selected_head_publisher.spl` | Typed expected-old vs target publication and receipt consumption |
| `src/compiler/80.driver/cache/publication/three_payload_generation_publisher_v1.spl` | Semantic packet admission; exact-operation outcome classification |
| `src/runtime/runtime_cache_host_authority_v1.c` | Native descriptor primitives; unsupported until qualified |
| `src/compiler_rust/runtime/src/cache_host_authority_v1.rs` | Existing owned platform boundary, not a replacement compiler/test runtime |
| `src/compiler_rust/runtime/src/cache_daemon_host_authority_v1.rs` | Existing journal/lock/GC platform owner, V3 additions |

Common contracts contain immutable copied records. Host registry state owns
descriptors, process/boot/root identity, current writer receipts, phase and
revocation. Simple semantic owners retain live compiler capabilities. Neither
side can manufacture the other side's admission from serialized fields.

## 2. Frozen types and host convention

Names below are exact V3 additions in the existing host-wrapper file. Opaque
wrappers each have one implementation field `opaque_handle: i64`; their
constructors do not confer authority. Every use validates registry kind,
owner instance, handle generation, root descriptor identity and live scope.

```text
CacheNamespaceAuthorityV3
CacheNamespaceScopeV3
CacheNamespaceSyncedObjectV3
CacheNamespaceRecoveryV3
CacheNamespaceGcCandidateV3

CacheNamespaceModeV3 = Publish(1) | Recover(2) | Collect(3)
CacheNamespaceLimitsV3 = {
  max_roots: i64, max_reader_domains: i64, max_lease_records: i64,
  max_synced_objects: i64, max_page_bytes: i64, max_candidates: i64
}
CacheNamespaceExpectedHeadV3 = Genesis | Selected(canonical_head_bytes: [u8])
CacheNamespaceCommitStatusV3 = Committed | Replayed | Conflict | Invalid |
  Unknown | Unsupported | Bounds | Cancelled | Stale | IoBeforeMutation
CacheNamespaceResolutionV3 = ExactCommitted | ExactNotCommitted | Unknown
```

All six limits are positive. Count caps are at most 65536; page bytes are at
most 1048576; journal bytes remain capped by existing
`CACHE_COOPERATIVE_MAX_JOURNAL_BYTES_V1 = 16777216`. All arithmetic is checked.
Provider-specific lower limits may refuse explicitly; silent truncation is forbidden.
`max_page_bytes` is also the cap for a single selected-head encoding, whose
actual V1 canonical encoding must pass its existing validator.

Raw functions below return `i64`. Handle-producing calls return a strictly
positive registry handle; zero is never a handle. Status calls return
`1=success/Committed`, `2=Replayed` (commit only), `0=Conflict`, `-1=Invalid`,
`-2=Unknown`, `-3=Unsupported`, `-4=Bounds`, `-5=Cancelled`, `-6=Stale`,
`-7=IoBeforeMutation`. Read calls return nonnegative byte counts, with zero
meaning EOF, and only negative errors. Their return domains must not be mixed.
An error after an irreversible write is `Unknown`, never `IoBeforeMutation`.
`Cancelled`, `Conflict`, `Stale` and ordinary refusal mean this attempt made no
publication mutation; they make no claim that another writer left the old head active.

In signatures, `bytes` expands to `[u8], i64 length`; `out` to mutable output
`[u8], i64 capacity`; `handles` to `[i64], i64 count`. No NUL termination,
pointer retention, negative length or integer truncation is permitted. Each
byte argument is copied/validated within the call; output capacity is checked
before any write or irreversible mutation. Names and argument order are frozen.

```text
rt_cache_host_namespace_available_v3() -> status
rt_cache_host_namespace_open_v3(root, lock, peer, readiness,
  nonce: bytes, writer_epoch, max_roots, max_reader_domains,
  max_lease_records, max_synced_objects, max_page_bytes, max_candidates) -> handle
rt_cache_host_namespace_begin_v3(namespace, mode, expected_head: bytes,
  live_reader_pin) -> handle
rt_cache_host_namespace_sync_object_v3(scope, object, kind: bytes,
  schema, digest: bytes, expected_size) -> handle
rt_cache_host_namespace_commit_selected_v3(scope, target_head: bytes,
  journal_append: bytes, synced_objects: handles) -> status
rt_cache_host_namespace_recovery_capture_v3(scope) -> handle
rt_cache_host_namespace_recovery_read_v3(recovery, part, offset, out) -> byte_count
rt_cache_host_namespace_resolve_operation_v3(recovery, writer_incarnation,
  operation_digest: bytes, generation, manifest_digest: bytes) -> resolution_status
rt_cache_host_namespace_gc_roots_page_v3(scope, byte_cursor, out) -> byte_count
rt_cache_host_namespace_gc_open_candidate_v3(scope, kind: bytes,
  schema, digest: bytes) -> handle
rt_cache_host_namespace_gc_unlink_candidate_v3(scope, candidate) -> status
rt_cache_host_namespace_finish_v3(scope) -> status
rt_cache_host_namespace_abort_v3(scope) -> status
rt_cache_host_namespace_close_v3(namespace) -> status
```

Bare scalar arguments are `i64`. `root/lock/peer/readiness/object/pin` are
existing issuer handles, not identity strings. Resolution status is a separate
domain: `1=ExactCommitted`, `0=ExactNotCommitted`, `-2=Unknown`; invalid,
unsupported, bounds and stale errors retain their negative codes.
Wrapper names are exactly the raw names without `rt_`; wrap each handle result
in its matching type and preserve refusal/status distinctions. No convenience
wrapper named `valid` may validate merely `handle > 0` as live authority.

`expected_head` is zero bytes for Genesis; otherwise it is the **old** complete
V1 selected-head canonical encoding. `target_head` is never empty and is the
**new** V1 encoding. The selected name and codec remain
`.simple-cache-selected-head-v1` and
`simple.cache.cooperative-selected-head.v1`. Reuse the existing
`cache_cooperative_selected_head_{encode,decode,valid}_v1` functions; no second
codec. Existing `ThreePayloadSelectedHeadExpectationV1`, which compares its
fields to the target packet, is not silently reinterpreted as an old-head CAS
expectation. Add `ThreePayloadSelectedHeadTransitionV3` in the existing
publisher with `expected: CacheNamespaceExpectedHeadV3` and
`target: CacheCooperativeSelectedHeadV1`; validate both independently.

## 3. Namespace, physical sync and publication

`open` validates live writer identity and descriptor-bound root, and refuses
unless all permitted writer, lease, explicit-pin and reader admission/mutation
paths participate in the **same cross-process per-root gate**. It does not
open an arbitrary second cache path. The initial profile serializes these
participants. In-process mutexes and public contribution booleans are not
substitutes. No global host handle-table mutex is held across Simple work.

`begin` lends this gate to one checked scope and captures head/journal identity.
The initial profile uses nonblocking gate acquisition: a busy independent
scope returns Conflict without mutation, not an unbounded wait. A child loan
under an existing scope does not reacquire or independently release its gate.
Publish requires a live same-root reader pin and the actual issuer's current
clock/boot/process identity; Recover and Collect require `live_reader_pin=0`.
The pin remains protected against revocation/expiry/GC through the durable
publication critical section. A wall-clock TTL copied at begin is insufficient:
the issuer must hold a loan or safely renew under the gate. No caller `now`
argument exists. Expected Genesis additionally requires positively admitted
empty history and absent selected head, not failure to read history.

`sync_object` validates an already opened immutable object descriptor, its
issuer-bound root/parent, kind/schema, exact bytes/digest and size. It calls
descriptor fsync and fsyncs the descriptor-bound containing directory if the
object's name was installed. The registry retains the descriptor and object
identity through commit. Reopening a pathname to sync different bytes fails.
The returned handle is scope-specific physical evidence; it is not a semantic
closure grant. Duplicate/aliased descriptor submissions cannot inflate the
closure. Semantic owners validate the exact required physical set against
their sealed packet before calling commit; host receipts preserve that set for
independent checking, not just a caller-supplied `closure_digest`.

`commit_selected` is valid only in Publish. It compares the captured old head
and live writer/pin again, checks the target and exact journal prefix/append,
and validates every submitted sync handle belongs to this live scope. A new
target has strictly greater revision and generation than a non-Genesis old
head; Genesis uses nonnegative values admitted by the existing writer.
Repetition of the exact already committed operation and identical target is
Replayed; operation-key reuse with different target/bytes is Invalid. An
unrelated current head is Conflict. Do not append twice for an exact replay.

The host performs, in order while retaining the gate:

1. Revalidate immutable descriptor set, pin loan and writer; refuse cancellation
   or conflict before beginning a new journal mutation. Before append, install
   and durably sync the operation-bound recovery intent described below.
2. Append exactly the admitted journal bytes and fsync the actual journal fd.
   Accepted prefix length/digest must equal the target fields; partial/torn
   records are never admitted by line count or presence of a newline alone.
3. Create an exclusive selected-head temporary relative to the bound root;
   write the canonical target bytes and fsync this exact fd.
4. Atomically replace the fixed selected-head name within that same directory.
5. Fsync that directory, then record the successful operation receipt. Clear
   the recovery intent durably only after the existing owners have established
   the complete admitted target. Return Committed only when the namespace can
   safely leave recovery-required state; otherwise retain Unknown and resolve
   this exact physically durable operation. Release or downgrade the protected
   pin only after the durable publication/retained-recovery transition.

File fsync alone does not persist the directory entry; Linux explicitly
requires directory fsync for that guarantee. Atomic rename visibility and
power-loss durability are different obligations. See the primary
[fsync](https://man7.org/linux/man-pages/man2/fsync.2.html) and
[rename](https://man7.org/linux/man-pages/man2/rename.2.html) interfaces.
The guarantee is conditional on the qualified filesystem/device honoring
these primitives; other providers remain Unsupported.

```text
Unmutated -> IntentDurable -> JournalStarted -> JournalDurable -> HeadReplaced -> HeadDurable
    |              |                |                 |               |             |
 refusal           +----------------+-----------------+---------------+-> Unknown   Committed
```

Only Unmutated can return a clean refusal. An error after intent mutation begins,
including a lost acknowledgement, is conservatively Unknown until same-owner
recovery establishes the exact operation. After HeadReplaced there is never a
rollback to old G. Cooperating readers must not admit a newly visible head
until directory durability succeeds or recovery reissues authority. A failed
directory fsync marks the namespace recovery-required. Cancellation after the
durable commit returns Committed/Replayed, not cancellation with old state.
Current head may later be competitor H even when this operation committed G+1.

`finish/abort` validate before consuming any handle. Publish finish requires a
terminal admitted state. **Recovery capture alone never authorizes release.**
An Unknown scope retains its gate and protected descriptors until exact
recovery resolves it, or transfers them to the existing writer's private
retained recovery/quarantine owner under a durable cross-process barrier.
The transfer must acknowledge ownership before consuming any child handle.
Abort drains submitted IO, never undoes publication, and follows the same
Unknown rule. A failed transfer or marker operation preserves the original
scope/gate and returns Unknown; it cannot restore the even GC epoch. Repeated close
returns the recorded terminal result, while foreign/wrong-kind handles fail
without releasing another scope. Namespace close refuses live children.
Process death releases OS locks but does not declare interrupted work complete.
Scope and child counters cannot wrap or ABA-reuse.

The fixed marker name is `.simple-cache-recovery-required-v3`. Install it by
exclusive temporary write, descriptor fsync, same-root replacement and parent
directory fsync **before** the first journal append. Its canonical UTF-8
header is `simple.cache.namespace-recovery-required.v3\n`, followed by the
nonnegative decimal lines `root_device`, `root_inode`, `namespace_epoch`,
`writer_incarnation`, `expected_head_length`, `target_head_length`, and then
exactly the expected and target canonical head byte strings in that order.
Lengths delimit the two bodies; no extra bytes are allowed. The target already
binds operation/generation/manifest and both prefix digests. This is an intent
and protection barrier, never a successful-publication receipt. Pending scope
descriptors/objects remain with the original or retained recovery owner;
while intent is unresolved, conservatively quarantine the entire root from GC.

Every namespace `begin`, including calls through an **already open handle**
in this or another process, rechecks this marker and actual selected/journal
identity under the shared gate. An unresolved, unreadable or malformed marker,
or inconsistent head/history, refuses Publish and Collect and admits only
bounded Recover. An in-memory cleared flag never overrides the durable marker.
If marker installation/directory sync fails, do not start journal mutation;
retain exclusion until the marker outcome is resolved or transfer is durably
acknowledged. On death, the next operation through any old or new namespace
handle must perform the same check before admission. If cleanup removed the
marker but its directory sync failed, state remains recovery-required locally;
after a crash the marker or the fully admitted target must be revalidated.
Only the existing recovery owner may clear intent after complete same-snapshot
physical **and semantic** recovery; removal and parent sync must succeed before
unquarantining the root. A captured diagnostic child that is later closed is
not such a transition.

## 4. Recovery and stable GC lease

Recover begin holds the same gate, even when the caller does not know the
current selected head. For this mode only, empty `expected_head` requests
capture, **not** a Genesis assertion. Nonempty bytes remain a compare guard.
`recovery_capture` works in Recover, Collect, or an Unknown Publish scope.
It duplicates/retains the actual root, selected-head and journal descriptors,
validates named-file identity, and captures a bounded immutable snapshot.
Recovery handle lifetime is nested in the scope; finish consumes its children.

`recovery_read` parts are `1=selected-head bytes` (empty iff admitted absence),
`2=raw bounded journal bytes`, `3=physical receipt`. Reads use captured
descriptors, never new path reads. The V3 physical receipt is a canonical
newline-delimited UTF-8 record, with no extra fields/trailing data:

```text
simple.cache.namespace-physical-receipt.v3\n
root_device\nroot_inode\nnamespace_epoch\nwriter_incarnation\n
selected_present\nselected_byte_count\nselected_sha256\n
journal_byte_count\njournal_sha256\nreader_epoch\n
```

Integers are canonical nonnegative decimal, `selected_present` is 0 or 1,
digests are lowercase SHA-256 of the actual captured bytes (including SHA-256
of empty bytes). Bytes are audit data, never re-importable handles. The Simple
journal/codec/closure owners validate semantic records and complete reachable
objects before reissuing durable prefix/selected generation authority. A
recovered DTO or checksum alone cannot reactivate a compile scope.

Protect all candidate durable roots before semantic closure checking; then
reissue admission against those same retained descriptors. This breaks the
recovery/GC circularity without trusting arbitrary roots. Torn or unadmitted
tail bytes may be retained diagnostically; do not repair/truncate them inside
capture. Any later repair is an explicit existing-writer operation.

`resolve_operation` asks about the exact tuple `(root identity, namespace,
writer incarnation, operation digest, generation, manifest digest)`. Host
physical evidence and Simple semantic admission must both agree before the
compiler reports ExactCommitted. ExactNotCommitted needs a complete admitted
history/checkpoint exclusion proof and no unresolved in-flight mutation for
that tuple. Missing/pruned/ambiguous evidence is Unknown, not “not found means
failed.” A newer selected head does not erase a retained successful receipt.

Collect begin acquires the same gate, checks an even reader epoch, and installs
a persisted odd epoch before inventory. All journal retention/build/release/
checkpoint roots, reader domains, explicit pins and filesystem leases belong
to one barrier revision. Include lease `referenced_manifests` **and**
`referenced_artifacts`; unknown liveness/PID reuse retains objects. Missing,
unreadable, malformed, unmapped or unprotected inventories fail closed.
No SQL/catalog absence, copied completeness bool, wall-clock guess or untyped
digest can authorize deletion. Handle/limit checks precede epoch mutation.

`gc_roots_page` exports the complete typed union captured by the existing
contribution owners, using the existing completion design's two variants:
`GenerationRoot(generation, manifest_object_ref)` and
`ProtectedObject(object_ref, protection_reason)`. The page stream is a V3
canonical UTF-8 transport, not a new stored root codec:

```text
simple.cache.namespace-roots.v3\n
total_member_count\n
G\ngeneration\nkind\nschema\ndigest\n
O\nkind\nschema\ndigest\nreason\n
... exactly total_member_count tagged records ...
```

Fields use existing object-kind and portable-reference validators; kind and
reason must be nonempty single-line ASCII tokens. Generation/schema are
canonical nonnegative decimal; digests are lowercase SHA-256. Reasons are
fixed tokens `lease_artifact`, `reader_object`, `explicit_pin`, `recovery_root`.
Sort/deduplicate complete encoded records bytewise before transport. Cursor is
an exact byte offset, with pages allowed to split records. EOF is authoritative
only after declared member count, full-stream validation and host completeness
admission; consumers may not treat a short page as EOF. The host retains the
entire bounded snapshot or an equivalent immutable owner lease through sweep.
If legacy kind mapping needs Simple admission, remain Unsupported until the
existing root-contribution owner is wired; do not guess a kind in native code.

`gc_open_candidate` opens one exact descriptor under this scope, validates its
kind/schema/digest, and returns a nested physical handle. The existing Simple
GC owner must separately hold `CacheVerifiedClosure` for this exact scope and
reject every candidate reachable from the complete root union. The raw host
primitive does not compute compiler semantic closure. Its only allowed
production caller is this gated existing owner; source refinement must show
there is no bypass path from public candidates/DTOs. Until that owner bridge
exists, the compiler GC-begin/public deletion gates remain closed even if the
host's individual descriptor calls are supported.
`gc_unlink_candidate` revalidates the same named object identity under the gate,
then unlinks and fsyncs its bound parent. Root-protected, changed or uncertain
objects cannot be deleted. An unlink followed by directory-sync failure is
Unknown; retry/recovery must not accidentally delete a replacement object.
Collection finish/abort drain IO and durably restore the corresponding even
epoch before releasing the gate. Neither accepts or changes a generation.

## 5. Formal obligations and counterexamples

Extend the existing formal project; do not rename its frozen modules or turn
its NotChecked receipt into proof admission. Abstract host operations must
declare assumptions and source-refinement obligations separately. Define
`NamespaceStateV3`, `ScopePhaseV3`, `DescriptorIdentityV3`,
`ExpectedHeadV3`, `OperationKeyV3`, `RootMemberV3`, `HostStepV3` and
`RefinesHostTraceV3` in an additive `HostNamespace` module only after the
formal owner approves the proof-source dependency revision.

Required theorem names are `committed_has_same_descriptor_durability_v3`,
`refusal_does_not_publish_this_attempt_v3`,
`unknown_does_not_imply_old_head_v3`,
`committed_cancel_never_rolls_back_v3`,
`recovery_matches_exact_operation_v3`,
`gc_retains_complete_root_union_v3`,
`scope_finish_preserves_generation_v3`, and
`forged_or_stale_handle_has_no_authority_v3`.
Each needs an inhabited positive execution, a rejected mutant, and explicit
native refinement evidence; theorem names or model transitions alone prove
neither compiled source equivalence nor a physical filesystem property.

| Counterexample ID | Mutation to kill / required observation |
|---|---|
| HABI-01 | Sync pathname B after opening A; descriptor identity mismatch refuses |
| HABI-02 | Rename succeeds, directory fsync fails; result Unknown, never clean refusal |
| HABI-03 | Expire/revoke pin between validation and commit; protected loan prevents it or commit refuses before mutation |
| HABI-04 | Expected old fields copied from target; old/target transition check rejects |
| HABI-05 | Competitor H wins; Conflict means this attempt did not publish, not head equals G |
| HABI-06 | Cancel/lost ACK after durable replace; exact operation recovers committed, never rolls back |
| HABI-07 | Pruned receipt, torn journal, missing history or equal generation/different manifest; no ExactNotCommitted/Genesis shortcut |
| HABI-08 | Artifact-only lease, PID reuse, missing pin page or incomplete root enumeration; deletion remains unavailable |
| HABI-09 | Scope/candidate ABA, wrong-kind abort, failed finish, counter overflow or Unknown→capture→finish→existing-handle begin/GC; no release/deletion before retained recovery, including marker failure and process death |
| HABI-10 | Alias/hardlink counted as independent source authority, or fourth payload opened through helper; broker rejects/counts actual opened inputs |
| HABI-11 | Same-generation forward/RR mismatch, omitted absence edge, old/new domain or SCC member; affected-domain issuer refuses |
| HABI-12 | Copied five-owner digest packet or structural semantic replay used as grant; live issuer/byte-profile verifier refuses |

L7 additionally retains: cold exactly source+initializer; warm exactly source+
prior-TLD+initializer; failed open attempts and control/pin/catalog IO counted
separately; descriptor-bound role admission; sealed macro/generic/default-trait
bodies; ordinary trait/aspect symbolic contracts; fail-closed unsupported
around/body-observing advice and bounded portable HIR. The RR delta must be
derived from same-generation forward reads, including absence and old/new
scope-domain/SCC closure, and published with summary/scope/object roots.
Three public filenames, forward/RR set equality in a toy model, or nonempty
record shape do not discharge these obligations.

## 6. Handoff and acceptance boundary

Implementation of typed wrappers and deterministic refusal checks is medium
and appropriate for Sol. Native durable authority, complete concurrent root
inventory and the semantic refinement proof are **difficult**, not Luna work.
Luna may only do mechanically bounded documentation/link or fixture-index
work after these names are frozen. Astra must review each authority-bearing
candidate before integration; parent is the merge owner.

The existing eight `L7E2E` step names remain unchanged. Correct L7E2E-08's
oracle: before publication mutation, a refusal leaves this attempt unpublished;
after a durable commit, cancellation cannot undo it; intermediate/lost-ACK
outcomes are Unknown until exact recovery. Assert the actual current head
separately, since a competitor may have advanced it.

No positive activation claim is permitted until immutable source dependencies,
same-owner native provider qualification, nonvacuous real descriptor/crash
tests, pure-Simple smoke/SSpec results and independent review are all recorded.
An unsupported provider and a correctly closed production gate are valid
partial deliverables, not a successful three-file production compile.

## 7. Implementation packet consolidation, 2026-09-12

The current handoff is the ten-packet appendix in the linked agent plan.
Scope is implementation completion only; validation, proof/spec execution and
production availability promotion are deferred. Existing validation plans are
backlog, not authorization to run them in these ten packets.

Read-only upstream observation: `origin/main` was
`c7c5bef3ca3580ed6742dce081c697435898e2db` (O); no fetch or push occurred.
The selected reconciliation candidate is
`877fa563005198d464784109f1fdbf84d4953a75` (R). Its parents combine host
`d13e95311b225857fc1ee54dc376c9191df3935f`, G
`756a21012839e67409ad40a926033c51e135787b`, and facet
`1ba1061d2be41b5f2db57ae6c8db36af64d1d268`, through pair merge
`fd9aeb98733e85672ea7f27e2f3f2f363c545cd6`. R is not upstream inclusion or
complete-source admission. It still lacks D0 common contracts. Parent must
preserve current-main features while porting exact owned-path deltas, never
replace main with R's older whole tree.

Shared-interface defining ownership is exclusive:

| Interface | Owner | Consumer boundary |
|---|---|---|
| Existing common physical TLD, scope/query/read/RR/execution/portable records and facet manifest | P01 | P02-P10 import, never recreate missing contracts |
| Frontend semantic references, bounded embedded sections and physical codec | P02 | P04/P09/P10 consume projections, not live grants |
| Five semantic scope issuers and private gateway installation | P03 | Actual source-owner identity, never copied evidence authority |
| Worker physical broker, body and admission interfaces | P04 | Cold-two/warm-three descriptor role accounting, no fourth payload |
| Authenticated affected domain, SCC and atomic RR generation | P05 | P10 receives same-generation forward/RR closure |
| Existing V1/V2 host API plus exact fourteen V3 calls in section 2 | P06 | Physical evidence only; preserve every existing symbol |
| Namespace, selected-head V1 codec, complete-root and GC closure ownership | P07 | P08/P10 borrow one gate and complete root union |
| Journal writer, expected-old/target selected head and exact recovery | P08 | P10 cannot reinterpret Unknown as rollback |
| Portable byte/profile semantic verification and verified CAS | P09 | Actual bounded bytes verified before executable use |
| Closure packer, generation packet and driver coordinator | P10 | Compose P01-P09, preserving existing routes/features |

Compatibility freeze: existing public DTO fields, constructors and exported
signatures are unchanged. New owner state remains private. A new required
public field or cross-owner signature needs explicit architect approval; it
cannot be smuggled into a helper or worked around with a duplicate contract.
Approved additive P04 entrypoint:
`read_three_payload_physical_files_from_root_v2`, with
`root: CacheRootAuthorityV1` prepended to the unchanged V1 broker argument
list and the same result/error type. It uses existing root-relative descriptor
open/size/pread/close operations and bounded cleanup. Legacy V1 cannot invent
root authority. Role bytes/header/digest checks do not prove distinct inode
identity: a physical alias guarantee stays unadmitted until P06 provides an
authentic existing or approved additive identity/equality hook.

The marker's expected and target head encodings **together** bind old/new
journal prefix digests; target V1 alone contains one accepted-prefix digest.
This corrects section 3's shorthand without changing the marker or host ABI.
Only the authentic existing recovery owner may clear quarantine after full
physical and semantic admission. No raw caller DTO is a substitute.

## 8. Final coding-interface freeze: blocked dependencies are injectable ports

This additive V4 coding contract supersedes the earlier instruction to wait
for live implementations before writing local algorithms. It authorizes
implementation against explicit unavailable adapters and test-only fakes,
**not** production gate changes. Existing V1/V2/V3 constructors, fields, ABI
and source-owner contracts are unchanged. All declarations below are planned
`.spl` declarations, not implementations or validated compiler syntax receipts.
No implementation or validation is performed by this docs-only freeze.

Capability-interface rules govern this shape: mutating trait methods use `me`;
do not use inert trait-header `with` sugar. Simple values can copy owner state.
Every free runner therefore returns the updated owner together with its Result,
including failure/Unknown branches. The caller must retain that returned owner.
Production owner/token validation is issuer-registry based, not a local copied
`closed` field, digest, constructor, domain enum or positive integer check.

### 8.1 Shared vocabulary, sole defining owner P03

Append only to existing
`src/compiler/00.common/cache_contract/semantic_scope_live_port_contract_v1.spl`.
This single completed-P01 file is explicitly handed to P03 for this pass;
no other common contract moves. Exact enum constructors and record fields:

```simple
pub enum L78BoundaryErrorV4:
    Unavailable
    InvalidRequest
    ForeignToken
    StaleToken
    ExpiredToken
    Bounds
    Incomplete
    Rejected
    Conflict
    Cancelled
    Unknown
pub enum L78AuthorityDomainV4:
    TestDouble
    Live
pub enum L78TokenKindV4:
    Scope
    AffectedDomain
    Namespace
    Closure
    Candidate
    Publication
pub struct L78AttemptKeyV4:
    root_digest: text
    generation: i64
    manifest_digest: text
    profile_digest: text
    operation_digest: text
pub struct L78OwnerTokenV4:
    domain: L78AuthorityDomainV4
    kind: L78TokenKindV4
    owner_instance: i64
    slot: i64
    epoch: i64
    attempt_digest: text
pub struct L78LimitsV4:
    max_items: i64
    max_bytes: i64
    max_steps: i64
pub struct L78OwnedResultV4<P, T>:
    owner: P
    outcome: Result<T, L78BoundaryErrorV4>
```

Constructors use exactly these named fields. Counts/steps are positive and at
most 65536; bytes positive and at most 16777216. Digests use existing canonical
validators; generation is nonnegative. Token slots/epochs use checked positive
integers and registry tombstones, never wrapping/reusing a live slot.
`attempt_digest` is SHA-256 of the UTF-8 canonical record
`simple.l78.attempt.v4\n`, then root digest, canonical decimal generation,
manifest digest, profile digest and operation digest, each followed by newline.
This digest correlates data; it does not authenticate an attempt.
The exact common helper is `l78_attempt_key_digest_v4(key: L78AttemptKeyV4)
-> Result<text, L78BoundaryErrorV4>`: reject malformed digest fields or negative
generation with `Err(InvalidRequest)`, otherwise return the canonical hash
above. A private full semantic-request digest is distinct. Never equate
`writer_instance_digest` with `root_digest`, or use `operation_digest` alone.
Live request-to-attempt binding remains the authentic issuer's responsibility;
fake owners already receive their explicit attempt key at construction.

### 8.2 P03 scope and five owner-hook ports

Define the public scope trait/closed adapter/runner in existing
`gateway/semantic_scope_authority_v1.spl`:

```simple
pub trait L78ScopePortV4:
    me acquire(request: SemanticScopeAttemptLiveRequestV1) -> Result<L78OwnerTokenV4, L78BoundaryErrorV4>
    me validate(token: L78OwnerTokenV4, request: SemanticScopeAttemptLiveRequestV1) -> Result<(), L78BoundaryErrorV4>
    me close(token: L78OwnerTokenV4) -> Result<(), L78BoundaryErrorV4>
pub struct L78ClosedScopePortV4:
    reason: text
```

Factory: `l78_closed_scope_port_v4(reason: text) -> L78ClosedScopePortV4`.
All three adapter methods return `Err(Unavailable)` regardless of reason.
Runner: `l78_acquire_scope_with_port_v4<P>(owner: P,
request: SemanticScopeAttemptLiveRequestV1) ->
L78OwnedResultV4<P, L78OwnerTokenV4>`, requiring P implement L78ScopePortV4.
It invokes acquisition and returns the changed owner even on refusal.

In existing `35.semantics/semantic_scope_issuers_v2.spl` define:

```simple
pub trait L78SemanticHookPortV4:
    me issue(request: SemanticScopeContributionLiveRequestV1) -> Result<L78OwnerTokenV4, L78BoundaryErrorV4>
    me validate(token: L78OwnerTokenV4, request: SemanticScopeContributionLiveRequestV1) -> Result<(), L78BoundaryErrorV4>
    me close(token: L78OwnerTokenV4) -> Result<(), L78BoundaryErrorV4>
pub struct L78ClosedSemanticHookV4:
    dimension_index: i64
    reason: text
```

Exact factories, each `(reason: text) -> L78ClosedSemanticHookV4`:
`l78_closed_declaration_hook_v4`, `l78_closed_trait_hook_v4`,
`l78_closed_aspect_hook_v4`, `l78_closed_macro_hook_v4`,
`l78_closed_body_hook_v4`; fixed dimensions 0/1/2/3/4 respectively.
These are local hook-dispatch indices; do not reinterpret an existing semantic
coverage dimension without the existing owner's explicit mapping. Every hook
method remains `Err(Unavailable)` until its authentic existing source owner
is wired. No synthetic five-token grant is issued from diagnostic projections.

Private registry scaffolds in existing `semantic_scope_live_owner_v2.spl`:
`L78ScopeRegistryEntryV4(token: L78OwnerTokenV4,
request: SemanticScopeAttemptLiveRequestV1,
contributions: [L78OwnerTokenV4], closed: bool)` and
`L78ScopeRegistryV4(owner_instance: i64, epoch: i64, next_slot: i64,
limits: L78LimitsV4, entries: [L78ScopeRegistryEntryV4])`.
Private `_l78_scope_registry_new_v4(owner_instance: i64,
limits: L78LimitsV4) -> Result<L78ScopeRegistryV4, L78BoundaryErrorV4>` creates
an empty bounded registry, never a capability. Every consume checks registry
issuer/kind/slot/epoch/request and five unique authentic contributions. No Live
entry issuance exists in the default adapter. Do not export a flag that enables it.

### 8.3 P05 affected-domain port

Define in existing `reference/reverse_reference_coordinator_v1.spl`:
`L78RrPlanV4(token: L78OwnerTokenV4, plan: AffectedQueryPlanV1)`.

```simple
pub trait L78AffectedDomainPortV4:
    me plan(scope: L78OwnerTokenV4, changes: [ChangedSemanticFacetV1], membership: [OldNewMembershipV1], groups: [VerifiedSccGroupV1], limits: L78LimitsV4) -> Result<L78RrPlanV4, L78BoundaryErrorV4>
    me validate(result: L78RrPlanV4, scope: L78OwnerTokenV4) -> Result<(), L78BoundaryErrorV4>
    me close(token: L78OwnerTokenV4) -> Result<(), L78BoundaryErrorV4>
pub struct L78ClosedAffectedDomainPortV4:
    reason: text
```

`l78_closed_affected_domain_port_v4(reason: text) ->
L78ClosedAffectedDomainPortV4`; every method returns `Err(Unavailable)`.
`l78_plan_affected_with_port_v4<P>(owner: P, scope: L78OwnerTokenV4,
changes: [ChangedSemanticFacetV1], membership: [OldNewMembershipV1],
groups: [VerifiedSccGroupV1], limits: L78LimitsV4) ->
L78OwnedResultV4<P, L78RrPlanV4>`, P implements the trait.
Plan algorithms can be coded using this port while authentic scope/old history
is absent. Missing absence edges, old/new membership, generation or SCC closure
must produce explicit errors, not broaden a public digest into authority.

### 8.4 P07 namespace and closure port

Define in existing `gateway/cooperative_namespace_gc_begin_authority_v1.spl`:

```simple
pub trait L78NamespacePortV4:
    me begin(mode: CacheNamespaceModeV3, expected: CacheNamespaceExpectedHeadV3, attempt: L78AttemptKeyV4, limits: L78LimitsV4) -> Result<L78OwnerTokenV4, L78BoundaryErrorV4>
    me roots(token: L78OwnerTokenV4) -> Result<CacheCooperativeNamespaceGcRootUnionV3, L78BoundaryErrorV4>
    me closure(token: L78OwnerTokenV4) -> Result<L78OwnerTokenV4, L78BoundaryErrorV4>
    me finish(token: L78OwnerTokenV4) -> Result<(), L78BoundaryErrorV4>
    me abort(token: L78OwnerTokenV4) -> Result<(), L78BoundaryErrorV4>
pub struct L78ClosedNamespacePortV4:
    reason: text
```

`l78_closed_namespace_port_v4(reason: text) -> L78ClosedNamespacePortV4`;
every method returns `Err(Unavailable)`.
`l78_capture_roots_with_port_v4<P>(owner: P, token: L78OwnerTokenV4) ->
L78OwnedResultV4<P, CacheCooperativeNamespaceGcRootUnionV3>`, P implements
the trait. A closure token needs authentic transitive closure of BOTH G and O
roots in one retained namespace. There is **no candidate/unlink port in this
pass**. Lease and root snapshots may be modeled, not blessed as live authority.
Publish-mode roots require an authentic publication-owner snapshot; never call
the Collect-only raw page ABI with a Publish scope as a workaround.
Finish/abort preserve owner and outstanding tokens on Unknown and other errors.

### 8.5 P08 publication port

Define in existing `publication/three_payload_selected_head_publisher.spl`,
not in `cache_writer_v1.spl`; this avoids adding a writer/generation import cycle.

```simple
pub enum L78PublicationPhaseV4:
    NotStarted
    Committed
    Replayed
    Unknown
pub struct L78PublishReceiptV4:
    phase: L78PublicationPhaseV4
    operation: L78AttemptKeyV4
    active_head: CacheNamespaceExpectedHeadV3
    authority: L78OwnerTokenV4?
pub trait L78PublicationPortV4:
    me commit(namespace: L78OwnerTokenV4, scope: L78OwnerTokenV4, affected: L78OwnerTokenV4, closure: L78OwnerTokenV4, expected: CacheNamespaceExpectedHeadV3, packet: ThreePayloadDurablePublicationPacketV1) -> Result<L78PublishReceiptV4, L78BoundaryErrorV4>
    me resolve(namespace: L78OwnerTokenV4, operation: L78AttemptKeyV4) -> Result<L78PublishReceiptV4, L78BoundaryErrorV4>
pub struct L78ClosedPublicationPortV4:
    reason: text
```

The four-token commit signature above is final: earlier messages omitting
`affected` and `closure` were corrected before this freeze. P08 must bind all
four genuine issuers to the same attempt, expected head and packet.
`l78_closed_publication_port_v4(reason: text) -> L78ClosedPublicationPortV4`;
all methods return `Err(Unavailable)`.
`l78_commit_with_port_v4<P>(owner: P, namespace: L78OwnerTokenV4,
scope: L78OwnerTokenV4, affected: L78OwnerTokenV4, closure: L78OwnerTokenV4,
expected: CacheNamespaceExpectedHeadV3, packet: ThreePayloadDurablePublicationPacketV1)
-> L78OwnedResultV4<P, L78PublishReceiptV4>`, P implements the trait.
Unknown may be a receipt phase or an error when no trustworthy receipt exists;
both retain ownership. Neither implies NotStarted/old head. Success/replay
requires Publication-kind authority matching the exact operation; fake authority
can demonstrate the model only. Current production adapter remains unavailable.

### 8.6 P10 composition seam

Define all new composition declarations only in existing
`gateway/cache_gateway_adapter.spl`, avoiding selected-head/generation cycles.

```simple
pub struct L78PipelinePortsV4<S, R, N, W>:
    scope: S
    affected: R
    namespace: N
    publication: W
pub struct L78PipelineRequestV4:
    scope_request: SemanticScopeAttemptLiveRequestV1
    attempt: L78AttemptKeyV4
    changes: [ChangedSemanticFacetV1]
    membership: [OldNewMembershipV1]
    groups: [VerifiedSccGroupV1]
    expected: CacheNamespaceExpectedHeadV3
    packet: ThreePayloadDurablePublicationPacketV1
    limits: L78LimitsV4
pub struct L78PipelineObservationV4:
    last_completed_stage: i64
    attempt: L78AttemptKeyV4
    publication: L78PublishReceiptV4?
    retained_tokens: [L78OwnerTokenV4]
    simulated: bool
```

`l78_plan_publish_with_ports_v4<S,R,N,W>(ports: L78PipelinePortsV4<S,R,N,W>,
request: L78PipelineRequestV4) ->
L78OwnedResultV4<L78PipelinePortsV4<S,R,N,W>, L78PipelineObservationV4>`.
S/R/N/W implement the four corresponding traits, longhand; compiler-supported
generic constraints may be used without changing names/argument/result shapes.
`l78_compile_publish_v4(request: L78PipelineRequestV4) ->
Result<L78PipelineObservationV4, L78BoundaryErrorV4>` is the non-injectable
production entry and remains `Err(Unavailable)`. No test mode, bool, environment
variable, public token or caller port can bypass that default.

Stages are 0=start, 1=scope acquire+validate, 2=affected plan+validate,
3=namespace begin+roots+closure, 4=publication commit or exact resolve,
5=acknowledged safe releases. Validate request/attempt identity before stage 1.
Forward all four tokens to commit. Cancellation/conflict before mutation does
not assert current head equals expected; Unknown retains namespace and scope,
and a later committed resolution never rolls back. Return updated ports on
every branch. `simulated` is observation data, not an admission bit. Fakes are
injected only into the model/core seam, never production construction.

### 8.7 Test doubles and exact unit seams

Four test-only fake classes implement the four traits, with no raw host calls.
Common exact fields on each: `case_name: text`, `owner_instance: i64`,
`epoch: i64`, `next_slot: i64`, `attempt: L78AttemptKeyV4`,
`limits: L78LimitsV4`, `events: [text]`, `active_slots: [i64]`,
`revoked_slots: [i64]`, `step_count: i64`.
`L78FakeAffectedDomainPortV4` additionally has `seed: AffectedQueryPlanV1`;
`L78FakeNamespacePortV4` has `seed: CacheCooperativeNamespaceGcRootUnionV3`;
`L78FakePublicationPortV4` has `seed: L78PublishReceiptV4`.
`L78FakeScopePortV4` has only the common fields.

Factories return those exact class types:
`l78_fake_scope_port_v4(case_name: text, owner_instance: i64,
attempt: L78AttemptKeyV4, limits: L78LimitsV4)`;
`l78_fake_affected_domain_port_v4` with the same four arguments plus
`seed: AffectedQueryPlanV1`;
`l78_fake_namespace_port_v4` with the same four plus
`seed: CacheCooperativeNamespaceGcRootUnionV3`;
`l78_fake_publication_port_v4` with the same four plus
`seed: L78PublishReceiptV4`.
Factories assert positive owner/bounds, use epoch/next_slot=1 and empty event/
slot lists, and issue ONLY TestDouble-domain tokens. Supplied seed authorities
must also be TestDouble; a Live-tagged seed fails setup, never gets promoted.

Allowed deterministic cases: scope `scope_ok`, `scope_unavailable`,
`scope_stale`, `scope_foreign`, `scope_expired`, `scope_close_unknown`;
RR `rr_ok`, `rr_missing_absence`, `rr_missing_scc`, `rr_wrong_generation`,
`rr_unavailable`; namespace `namespace_ok`, `namespace_unknown_finish`,
`namespace_unknown_abort`, `namespace_missing_artifact`,
`namespace_truncated_roots`, `namespace_unavailable`; publication
`publish_committed`, `publish_conflict`, `publish_unknown`,
`publish_unknown_then_committed`, `publish_unavailable`.
Unexpected case/operation order must fail the test, not silently return success.
Event strings are exactly `scope.acquire/validate/close`,
`affected.plan/validate/close`, `namespace.begin/roots/closure/finish/abort`,
`publication.commit/resolve` (one string per operation, expanding the slash
notation, e.g. `namespace.roots`). Enforce slot ownership, epoch, revocation,
attempt identity, count/byte/step budgets and Unknown retention in fake state.
These exercise actual core transitions, not filesystem or issuer authenticity.

U01 helpers: `l78_expect_scope_events_v4(actual: [text], expected: [text]) -> ()`;
`l78_expect_affected_plan_v4(actual: L78RrPlanV4, expected: AffectedQueryPlanV1) -> ()`.
U02 helpers: `l78_expect_namespace_retained_v4(port: L78FakeNamespacePortV4,
token: L78OwnerTokenV4) -> ()`; `l78_expect_publication_phase_v4(
receipt: L78PublishReceiptV4, expected: L78PublicationPhaseV4) -> ()`.
U03 factory `l78_fake_pipeline_ports_v4(scope: L78FakeScopePortV4,
affected: L78FakeAffectedDomainPortV4, namespace: L78FakeNamespacePortV4,
publication: L78FakePublicationPortV4) ->
L78PipelinePortsV4<L78FakeScopePortV4,L78FakeAffectedDomainPortV4,L78FakeNamespacePortV4,L78FakePublicationPortV4>`;
helper `l78_expect_pipeline_trace_v4(observation: L78PipelineObservationV4,
actual: [text], expected: [text]) -> ()`.
Assertions use existing built-in matchers. Missing test behavior uses
`fail("L78-V4: implementation missing")` or `assert(false)`, never skipped
success, no-op or tautological gate checks. Unit authoring may proceed without
live dependencies; execution and production qualification remain separate.

### 8.8 Compiler spelling correction and composition receipt

This amendment supersedes only the reserved-identifier spellings in sections
8.5–8.7. The bounded U03 compiler attempt rejected `namespace` as a reserved
keyword. Use `namespace_port: N` in `L78PipelinePortsV4` and
`namespace_port: L78FakeNamespacePortV4` in the U03 factory. Publication
`commit`, `resolve`, and `l78_commit_with_port_v4` call their first argument
`namespace_token: L78OwnerTokenV4`. Types, positional ordering, token kinds,
and `namespace.*` event strings do not change. No alternate public contract
or compatibility alias using the reserved spelling is required.

The P10 coding candidate is immutable commit
`8eef058617d5e7903347da9f49a1a46b23fda18d`, parent
`1826de9ba29ae5f54689f3f8d534f948956e4fe3`, changing only
`src/compiler/80.driver/cache/gateway/cache_gateway_adapter.spl`.
It consumes the existing durable publication packet and the four frozen
ports; it defines no new packer authority or selected-head implementation.
The target attempt binds packet root/durable generation, manifest, operation,
and scope semantic profile, without equating the pinned input generation to
the target or writer instance to cache root. Twelve calls are reserved before
acquisition; an Unknown or malformed commit acknowledgement receives at most
one exact-operation resolution. Unknown retains owners. A known terminal
receipt survives cleanup failure as stage 4 with the exact unacknowledged
tokens; successful cleanup is stage 5. The model seam accepts TestDouble
tokens only and the non-injectable production entry stays Unavailable.

This is an authored coding receipt, not compile, test, or formal acceptance.
Integration must first supply the corrected versioned P05 `L78RrPlanV4`
token-plus-plan interface and final P03/P07/P08 dependencies. In particular,
P05 closes only its own AffectedDomain token, never the Scope token.
Generation publisher must not import the selected-head publisher (cycle),
and pure closure packers must not issue the P07-owned Closure token.
