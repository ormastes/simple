# Astra review: incremental build metadata and TLDR freshness

<!-- codex-architecture -->

Date: 2026-10-08. Status: **review recommendations only; no implementation or performance qualification**.

## Scope and evidence

The reviewer read all 803 lines of `C:/Users/user/Downloads/simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md` (65,281 bytes, SHA256 `128a5f947662e9d10bc8267aa57bac455a243251af29df4187df4f6be47b2b3a`). The byte-identical repository copy is [the proposal](simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md). Proposal line numbers below refer to that document.

Two source baselines were inspected through immutable Git blobs: main `2e43233b11fbbd837535d9313a168f729fad7f46` and the active compiler source `6bf3276a4344923bea1dae84c933b2aeda13db58`. The dirty working checkout is a different baseline; absence from its filesystem is not evidence of absence from either reviewed tree. Source availability, integration, native execution and performance qualification are separate assertions. This review launched no compiler, modified no holder, and ran no previously passing tests.

## Recommendation

Accept the proposal's separation of immutable source identity, binary publication, TLDR freshness, tests and SCM attachment. Reuse `CompileSnapshotV1`, the existing cache gateway, semantic read manifests and scheduler. Introduce source-change events as adapters into those authorities, not a second source snapshot or cache authority.

Prioritize an admitted immutable source epoch and retained reader pins, with measured single-flight reuse, in parallel with metadata shadow recording. The proposed metadata-first sequence (lines 758–765) delivers useful history but does not itself meet the user's imported-TLDR compilation target of 0.1 seconds. Keep the full metadata/SCM scope in the plan while giving the existing compiler hot path an independent acceptance gate.

## Exact source anchors

Paths and lines in this table are relative to the named Git revision, not the current working copy.

| Revision | Path and lines | Observed contract | Git blob |
|---|---|---|---|
| main | `src/compiler/10.frontend/frontend_parse_cache.spl:23–34,73–117` | Full source-byte key, driver scope, codec version; missing scope disables cache. Scope memo is process state. | `a787f04a3df3a22314bd820716d76b480a91cd4a` |
| main | `src/compiler/80.driver/driver_hir_cache.spl:84–109` | Closure hashes every surface path/content/length/name; source hash and entry flag participate. | `0224e05bbca4c2ce34c2c3e40449c0a485cfae00` |
| main | `src/compiler/80.driver/cache/package_tldr_metadata.spl:9–16,40–62,219–300` | Existing config fields, TLDR metadata, separate interface/action keys; interface key includes SMF digest. | `0b6d78e991ff6ba022d3816967f8e9f3a00f8713` |
| main | `src/lib/scv/parser_session.spl:8–18,91–94,110–112` | Honest full-reparse fallback; edit records do not imply retained-tree incremental parsing. | `9ab58565d4ef8829174da99016cd3d73aa5d9d90` |
| main | `src/lib/scv/metadata_db.spl:8–16,29–64` | Existing SDN snapshot/WAL, explicit insert WAL ownership, schema version and metadata tables. | `144d9ea77529e4ccc435f0f3175421f7346ef734` |
| main | `src/lib/editor/document/transaction.spl:3–4,14–45` | Ordered byte-offset edits and inverse transaction; not necessarily a canonical minimal diff. | `cb3a2a469348acc7097486bb4382f5a61c4ecf4d` |
| 6bf | `src/compiler/00.common/cache_contract/snapshot_contract_v1.spl:28–80,82–100` | Resolution order, absence and directory witnesses, generated inputs, config/target/producer/runtime/toolchain identities; dependency roles distinguish semantic hashes from retained CAS objects. | `90a84ee62d596ef363b371dd9a153ed431b36763` |
| 6bf | `src/compiler/10.frontend/snapshot/compile_snapshot_freezer.spl:180–196,198–250,261–283` | Selected-source witness matching, negative-candidate checks, namespace/generation validation and nonempty capture requirements. | `5a5867796c2c1170b60f9786a66b289082fa3156` |
| 6bf | `src/compiler/00.common/cache_contract/cache_gateway_v1.spl:26–49` | Transport-neutral read facade, direct-read pin lifecycle and distinct writer authority. | `90382dcadbe0f23c5198b96de29c4245c5e9b9b6` |
| 6bf | `src/compiler/80.driver/cache/gateway/cache_gateway_adapter.spl:55–114` | Pin binds process, boot, epoch, generation and manifest; host authority validates it; catalog generation mismatch rejects. | `9223a3e750a29ad26c2e7cf54d1911c9a6523d68` |
| 6bf | `src/compiler/00.common/cache_contract/semantic_query_read_manifest_v1.spl:13–37,177–200` | Complete/Conservative/Unknown coverage, query/profile identities, ordered facets/fingerprints/witnesses and bounded decoder. | `1bf6ffaa127ecc682fa175ae44a90a8e3b699c90` |
| 6bf | `src/compiler/00.common/cache_contract/physical_tld_v1.spl:3–5,16–18,27–73` | Physical generated metadata has no extraction authority; existing bounded codec budgets. | `f77d76be3d31cd47e395a1d41cfd58aa819d9c21` |
| 6bf | `src/lib/common/task_runner/scheduler.spl:88–102,125–163,166–202` | Exact-attempt reap/accept, output verification, transitive blocked dependents and bounded crash retry. | `b1d3bc616daf6ec6cb8f7d94bc3c5ee0b9ff810f` |

The main-tree detail design `doc/05_design/static_when_tldr_build_pruning.md:27–39,60–84,92` supplies the intended sealed-universe, coverage and negative-dependency rules. It is a design reference, not proof every described producer is wired into the active compiler.

## Corrections and decisions required before implementation

### 1. Separate semantic transition identity from event provenance

Proposal lines 601 and 629 require equal adapter digests for equivalent changes, but the proposed events include origin, transaction ID and sequence. Equivalent edits also have different valid edit scripts: a replacement, two insertions, or a reconciled before/after transition. Hashing the whole event cannot meet the stated equivalence contract.

Define two identities: a semantic transition digest over canonical old/new snapshots and path/kind/content transitions, and an event-envelope digest including origin, sequence and transaction lineage. Semantic cache eligibility uses the former or the resulting snapshot, never actor provenance. Preserve the actual edit script for incremental parsing without requiring all editors to generate the same script. Explicitly choose whether offsets are sequential against intermediate versions or all relative to one old snapshot; validate and encode that convention.

### 2. Frozen validity is distinct from current-worktree freshness

The delta algorithm's final current-source comparison and `STALE_SNAPSHOT` wording (lines 299–323 and 461) can conflict with lines 574 and 582: an old immutable snapshot remains certifiable after HEAD advances.

Use separate predicates `Verified(snapshot, scope, policy)` and `Current(workspace, snapshot)`. If captured bytes or a required immutable pin are lost, verification fails. If only the mutable workspace advances, retain the old verified result, report that it is not current, and never attach it to the new revision. Otherwise continuous editing can starve all asynchronous certification and waste valid work.

### 3. O(1) source admission needs an actual immutable owner

An unchanged watcher counter, cached Git status, timestamp tuple or application-held boolean is not an immutable source epoch. External writes, watcher overflow, path replacement and process restart must invalidate its use for mutable files.

The fast path should consume an already admitted `CompileSnapshotV1` and retained bytes/objects under existing reader authority. The admission producer pays complete capture and resolution validation once. Workers receive a bound snapshot reference; they do not rescan the entire mutable checkout independently. Reuse across requests requires the source owner to account for all mutations or recapture. Document the trust boundary and cost separately: constant-time handle admission does not make initial snapshot creation constant-time.

### 4. Body-edit cutoff is not implemented by the current keys

`package_tldr_interface_key_v1` includes `header.smf_digest` (main lines 270–283). If the SMF contains body/object payloads, a private-body change can change that key even when public declarations are identical. The HIR closure key also hashes full surface content (main `driver_hir_cache.spl:84–109`). Thus the proposal's minimal downstream rebuild expectation is a new behavior, not an existing consequence of `PackageTldrHeaderV1`.

Keep three identities explicit: physical container/object digest, semantic interface projection digest, and executable/action digest. Do not simply remove SMF/source fields from current keys. First make consumers declare exactly which facets they read, including inline/generic bodies, constants, initializer effects, trait/coherence candidates and woven aspects. Only then introduce a versioned projection key with fresh-vs-reused parity tests.

### 5. Target-independent sharing needs a policy classification

Current `ConfigVariantKeyV1` contains target/backend/features/build mode/ABI/options/environment, but no explicit aspect or capture field. Its generic options fields do not prove that every effective semantic input is actually supplied. Hashing all invocation fields would be conservative yet prevent reuse between different entry/output jobs.

Specify per-product dependencies: lexical/source AST may share across targets only if grammar, conditional syntax policy and all parse-affecting inputs match; selected imports and semantic TLDR need sealed guard configuration and effective transforms; object/link products need target layout and backend/runtime/toolchain identities. Include captured typed values or immutable capture snapshots and aspect provider/version/order. Output filename, worker count, log verbosity and request ID are execution metadata unless actual source semantics read them. Unsupported or ambient semantic inputs must make that product noncacheable, not receive invented defaults.

### 6. Static guards require negative and membership dependencies

False branches cannot disappear from all metadata: changing configuration or adding a formerly absent candidate may activate them. Bind guard table, universe seal, selected config, ordered resolver candidates and directory membership witnesses. A guard with unknown member, wrong seal or malformed syntax must not evaluate false.

Separate structural scan coverage from semantic body coverage using existing Complete/Conservative/Unknown tags. Complete import-region scanning cannot certify all macro/inline/initializer/coherence effects. A conservative manifest may authorize a conservative full closure, but cannot authorize selective pruning that assumes missing edges are absent. Cyclic summaries require bounded SCC/fixed-point completion; publishing an intermediate iteration as a complete summary is invalid.

### 7. TLDR, physical TLD, function ABI headers and SMF are different products

The proposal correctly excludes Markdown TLDRs. It should additionally map its freshness verifier onto the existing distinct representations: `PackageTldrHeaderV1`, physical generated TLD records, public semantic summaries, and the function-header admission path used by the active compiler. Container validity is not semantic completeness; a package header is not automatically a full project summary. `__init__.tld` coverage must include module membership and initialization semantics.

A hybrid `.smf/` directory is a new manifest representation, not permission to change the existing packed wire schema or loader. Retain direct CAS references with typed roles: semantic fingerprints must not be treated as object-retention edges. Define whether freshness asserts correctness of referenced content, current availability, or both. A historically valid receipt remains historical evidence after GC, but a current reuse claim needs live required objects.

### 8. Cross-worker parsed sharing must save real work

The reviewed gateway has read pins; this does not by itself establish a wired single-flight parsed-result producer. Specify the actual producer, owner, consumer and transport. An untrusted encoded header that each worker reconstructs, rehashes and revalidates may cost more than the original parser. Prior session measurements found precisely that in the rejected codec draft; do not revive it merely to claim one producer parse.

Within a process, retain immutable admitted typed results under the compilation owner and root their arrays for their full lifetime. Across processes, never transport raw pointers or runtime-specific symbol IDs. Use existing authenticated output handoff/read authority for immutable artifacts; bind the complete action identity and preserve independent validation at an untrusted ingress. Measure remaining decode, validation, hash, allocation and IPC costs separately from parse count.

### 9. Single-flight must specify failure and reclamation

Use one keyed attempt owner with an explicit generation and terminal result. Waiters subscribe to that attempt and validate the admitted result; they cannot turn a missing result into success. Owner crash permits recovery only after the existing process/lease lifecycle establishes termination; a late old-attempt result cannot replace a successor. Failed admission is not a reusable successful cache entry.

Reuse the scheduler's reap/accept/output-verification and blocked-dependent semantics. Keep independent jobs progressing. Bound queue length, waiter count, retained bytes and retry count. Cancellation of one waiter must not revoke another's pin; cancellation of the last reader may reclaim only after active producer/publication obligations settle. Publish artifact bytes before the manifest/head that names them, and retain old-generation objects until all readers release or expire under trusted authority.

### 10. Receipts and notes need an explicit lattice and durable owner

Binary, TLDR, test and SCM states are independent components, not a single success enum. Define qualification as a conjunction over required exact identities and terminal outcomes. Missing, unknown, crashed, pending or stale-required evidence is nonpass. A TLDR failure need not delete an independently valid binary; an SCM outage cannot retroactively change compilation semantics.

Proposal lines 445 and 457 leave attachment policy ambiguous: the DAG waits for mandatory test qualification before attaching, whereas `TLDR_VERIFIED` alone may create a TLDR note. Choose typed independent freshness notes or combined qualification notes; never use one label for both. Local notes must merge receipts as typed records under expected-old-ref publication. No note mutation participates in source or action identity.

The existing SCV database already owns explicit WAL insert replay. New binary segments and SDN projections need one transaction owner, an ordering/commit record and crash-recovery rule; do not create two independent journals that both claim authority. Define durable enqueue before reporting an asynchronous job ID and who supervises workers after foreground exit. Standalone compile remains correct without SCV, Git or a daemon.

### 11. Source-tree identity must bind checkout semantics

A Git tree alone is insufficient for materialized bytes under attributes, line-ending conversion, LFS, symlinks, junction aliases, generated inputs or unsaved buffers. Bind actual admitted bytes and resolution/path policy, with an authenticated relationship to the intended Git tree when attaching a note. Do not require raw index-file bytes to stay unchanged: index stat-cache refresh is different from staged mode/blob/path identity. Neither content equality nor a resolved path alone proves trusted containment or correct alias resolution.

## Proposed formal invariants

These are acceptance contracts, not statements that current code already proves them.

1. **Snapshot binding:** every consumed source byte belongs to the admitted snapshot; no mutable pathname reopen silently changes its identity.
2. **Reuse equivalence:** a hit requires matching product schema/producer/policy and complete relevant read witnesses; accepted reuse yields the same semantic artifact and required diagnostics as fresh execution.
3. **Negative completeness:** changes to candidate membership, lookup order or a recorded absence invalidate every affected query even without a prior positive dependency edge.
4. **Guard provenance:** evaluation uses one matching universe/table/config tuple; unknown coverage cannot authorize selective pruning.
5. **Publication:** a visible successful manifest names only complete, validated, retained objects; old readers continue using their pinned generation.
6. **Attempt isolation:** only the active reaped attempt may settle a task; crash, timeout, cancellation or absent receipt never implies successful output.
7. **Qualification:** qualified success implies every required terminal receipt matches the exact snapshot, binary and policy; scheduling is not evidence of completion.
8. **History isolation:** advancing HEAD or the worktree does not change old snapshot facts; attaching a receipt never certifies another tree.
9. **Semantic identity:** actor, note ref, event sequence and output destination do not enter semantic keys unless the language actually reads them.
10. **Bounded lifetime:** allocations, decoder limits, queues, retries and reader retention have explicit caps and release paths; no caller-mutated admitted array or cross-process pointer becomes trusted semantic data.

## Proposed acceptance tests

All cases below are **UNRUN proposals**. They must use production entrypoints and independently verified outputs; maps populated only by a test are insufficient evidence of real producer wiring.

| ID | Fixture / operation | Required result |
|---|---|---|
| META-01 | Same before/after bytes via IDE sequential edits, Spipe replacement and SCV reconciliation | Equal semantic transition/root; distinct truthful provenance permitted. |
| META-02 | UTF-8 and CRLF edits with sequential and old-snapshot offset modes | Exact bytes and inverse behavior; wrong convention rejected. |
| META-03 | Watch overflow, bypassing writer, process restart and path replacement | Fast mutable epoch refused; recapture or verified immutable snapshot used. |
| META-04 | Start postcheck on A, edit/commit B while A runs | A may verify and attach only to A; B remains pending; no starvation/relabeling. |
| META-05 | Private body, public signature, inline body, constant and initializer changes separately | Reuse/cutoff follows actual consumed facets; current broad-key misses recorded honestly. |
| META-06 | Add higher-priority module, overload, trait implementation or aspect target | Negative/membership witnesses invalidate affected consumers. |
| META-07 | Same source across two targets and across two entry/output jobs | Share only target-independent eligible products; effective aspect/capture change invalidates. |
| META-08 | Wrong guard universe with identical numeric IDs; malformed inactive guard; cyclic imports | Reject wrong seals/errors; complete bounded SCC result before publication. |
| META-09 | Concurrent processes request identical TLDR action | One admitted producer attempt; waiters obtain same verified result; measure total work, not just parser calls. |
| META-10 | Producer dies before artifact, between artifact/manifest, and after publication | No partial success; correct recovery; old-attempt completion cannot overwrite successor. |
| META-11 | Cancel one waiter, expire a reader, run GC while another reads | No dangling result; retained reader succeeds or explicit pin failure; bounded release. |
| META-12 | Corrupt/truncate SDN/WAL/binary frame; crash each publication boundary | Recover committed prefix or rebuild; unsupported critical records never admitted. |
| META-13 | Missing CAS object behind valid historical note; tampered typed receipt | Historical note remains distinguishable; current reuse misses/fails, never fabricated coverage. |
| META-14 | Failed test after binary publication; missing worker receipt; notes unavailable | Binary preserved; required qualification nonpass; independent TLDR state remains truthful. |
| META-15 | Concurrent note writers, changed index, reordered receipts | Typed conflict handling; exact tree/ref compare-and-swap; no unexpected commit/amend. |
| META-16 | Git checkout with exact CRLF/LFS/symlink materialization plus sparse/generated inputs | Correct physical source binding and scope; no raw-tree-byte shortcut or missing-input pass. |
| META-17 | Packed SMF vs directory/CAS representation | Same semantic contents, link/runtime behavior and diagnostics; existing loader compatibility. |
| META-18 | Disable/delete optional metadata, notes and daemon | Correct standalone fallback; zero mandatory SCM/runner processes. |
| META-19 | Production parser/HIR cache under unchanged, comment, body and public edits | Fresh/reused diagnostic parity plus exact parse/hash/read/lower/emit counters. |
| META-20 | One imported module, representative project and 80-job contention | Cold/warm median/p95, CPU, peak RSS, bytes/opens, IPC and lock time; explicitly measure the 0.1-second goal. |

## Suggested parallel ownership and merge order

1. **Contract owner:** map proposed roots/events onto existing snapshot/read contracts; decide semantic vs provenance encoding, policy partitions and coverage. Freeze interfaces first.
2. **Compiler performance owner:** immutable source admission, retained parsed-header ownership and single-flight wiring; use current hot-path baselines. Do not block this lane on Git notes or SMF repacking.
3. **Metadata owner:** IDE/Spipe/SCV adapters and one durable journal, initially shadow-only; compare transition identities and reconcile incomplete history.
4. **Qualification owner:** existing scheduler integration, exact binary/snapshot receipt joins and typed local SCM attachment. Depend on contract interfaces, not compiler internals.
5. **Reviewer/verification owner:** differential correctness, concurrency fault injection, memory lifetime and independent timing. Admit each feature only after its own gates; keep remote transport and SMF layout separate changes.

Merge contracts and shadow observation first; enable each optimization only after its production path is demonstrated and measured. Preserve the standalone fallback throughout. Reuse existing live bootstrap work; do not rerun failed unchanged producers or previously green criteria to manufacture progress. This document does not authorize release, assert native PASS, or claim cross-worker sharing is complete.

## Final integrated-design review

2026-10-08: reviewed the integrated architecture, detail design, feature/NFR requirements and parallel/acceptance plans. The first review found no P0 and two P1 contract gaps: header readiness was insufficiently separated from later object failure, and header-only reuse lacked an explicit diagnostic observer policy. It also requested a distinction between summary action inputs and computed public-facet output identity.

The focused successor review checked only those changed contracts. **Design-only verdict: accepted; both P1 findings and the key-identity clarification are closed.** Detail design section 3 now makes each stage independently committed and preserves an admitted header after object failure. Sections 4–5 distinguish action-input keys from output facet digests and require policy-bound body-validation evidence for full diagnostics. REQ-IM-016 adopts the observer distinction. The acceptance table includes header-survives-object-failure and diagnostic-observer-coverage cases. Frozen-versus-current identity, conservative V1 fallback before V2 witness completeness, and independent TLDR/SCM/test states were already consistent in the full review.

Reviewed content pins (SHA256):

| File | Digest |
|---|---|
| `doc/04_architecture/incremental_build_metadata_20261008.md` | `7f8219026c96d24c4cd1782f8c637eca0fbf5aff6725654d2b4f5c19522ee72d` |
| `doc/05_design/incremental_build_metadata_20261008.md` | `15fe60d4ac826380c18940c35a27412a4adff80c06cccdbf715c45b5add68abd` |
| `doc/02_requirements/feature/incremental_build_metadata_20261008.md` | `443e92430ec05217f581122154e97a5eb13099a6cdf6230f479a2c5fcb71baa6` |
| `doc/03_plan/sys_test/incremental_build_metadata_20261008.md` | `40ca41b75e202eefb59026284e5b64ab84b73cd1cb243e7aa0c0651ab0c3a6fb` |

This accepts the specified design contract, not its implementation. Model checking, native semantic parity, concurrency/GC safety, full diagnostic coverage and the 100 ms performance target remain unverified. No runtime checks were launched and no production source or active holder was modified during this review.
