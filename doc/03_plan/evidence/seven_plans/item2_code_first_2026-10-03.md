# Item 2 implementation and test-source wave

User steering: implement the complete selected scope and its test code first.
An unavailable admitted test runner is an execution gate, not permission to stop
writing the selected production owners. Authority A / Adapters A / Operating B /
Retention A and the 36 functional plus 15 nonfunctional requirements remain.

This is a source-progress record. **Execution is UNVERIFIED.** No authored test,
static diff check, provider fixture or source inventory is RED/GREEN, coverage,
crash durability, cross-platform qualification, or a measured scale result.

## Integrated source contracts

| Area | Production owner | Source behavior |
|---|---|---|
| Canonical protocol | `src/lib/scv/db_canonical.spl`, `db_patch.spl`, `db_patch_normalize.spl` | Tagged domain framing, minimal unsigned encoding, Unicode NFC, duplicate-key rejection, typed patches and content identities |
| Reducer | `db_reducer.spl`, `db_schema.spl`, `db_remove_wins.spl` | Scalar/list conflicts, field authority, observed add-wins and explicit causal remove-wins sets, constraints, original actor/counter collision detection and retained semantic bases |
| Snapshot | `db_snapshot.spl`, `db_snapshot_values.spl` | Strict complete versioned recovery with semantic digest verification, quotas and no trailing data; v2 includes actor/counter/base registry |
| Admission | `db_admission.spl` | Actual Ed25519 verification, independently pinned scope policy, key windows/revocation, CI append-only authority, repeated verification at effect boundary |
| Local storage | `src/app/scv/db/local_store.spl`, `local_apply.spl` | SJ-owned compare-and-publish, complete immutable generation, bounded no-follow reads, safe staging, fsync barriers and retry durability; authority/schema context bound in stored header |
| Offline identities | `offline_actor.spl` | Durable reservations conservatively rotate a random incarnation on every reservation, including reuse after restoring an old counter and old copied handle |
| Evidence | `db_evidence.spl`, `db_ci_ingest.spl` | Pinned config/expectation/reproduction revisions, provider identities, manifest coverage, provider DTO normalization and receipt-gated cursor transition rules |
| Evidence storage | `src/app/scv/db/evidence_store.spl` | External typed-envelope CAS, quota checks before IO, no-replace publication, actual byte readback and dependency-digest binding |
| GitHub discovery | `src/app/scv/db/github_provider.spl` | Bounded real gh API transport, scoped paginated runs and attempt jobs, tracked reruns, sanitized failure categories, injected transport tests and opt-in live read scenario |
| Bridge and retention | `db_bridge.spl`, `db_retention.spl` | Separate intent/delivery state, uncertain-effect reconciliation rules, exact retention boundary, closure pins, deduplicated sufficient-statistic rollups, honest resolution and resnapshot invariants |
| Settlement receipts | `db_receipt.spl` | Actual signed receipt bytes, pinned authority, hash-chain binding and allocator regression checks; Git ancestry remains an independent transport proof |
| Allocation projection | `db_allocation.spl`, `db_identity_snapshot.spl` | Admission before allocation, preserved canonical UIDs, contextual aliases, recursive typed-reference projection and complete allocator snapshot |
| Patch interchange | `db_patch_codec.spl` | Strict versioned round-trip of every patch field, operation, structured reference and signature; original digest checked before normalization |
| Receipt index | `db_receipt_index.spl` | Three identical immutable projections, signed successor/history checks, exact-ref Git append and readback; signed profile/ruleset examination is evidence only, not production admission |
| CI persistence | `src/app/scv/db/ci_store.spl`, `ci_readback.spl` | Multiplexed durable discovery and cursor CAS after actual Git tree/blob, signed receipt and external evidence closure checks |
| Bounded pages | `db_pages.spl`, `src/app/scv/db/page_store.spl` | Immutable hash-bucket pages, canonical manifest, bounded affected-page updates and durable page/manifest publication; authoritative transaction source is now integrated separately; runtime/scale remain unverified |
| Host paths | `src/lib/nogc_sync_mut/io/path_identity.spl` | Existing-path kernel resolution on Windows and realpath on POSIX, explicit errors and no lexical fallback; local generation/actor owners consume it |
| Recovery journal | `src/app/scv/db/settlement_journal.spl` | Signed candidate and exact tree/blob inventory persisted before publication; actual remote ancestry read-back advances only to awaiting-index |
| Quarantine | `src/app/scv/db/quarantine_store.spl` | Bounded uncompressed patch bundles imported into external CAS; reopening revalidates bytes; promotion preparation checks independent signature/metadata/ACL policy |
| Trusted configuration and CLI | `db_policy_codec.spl`, `src/app/scv/db/commands.spl` | Independently pinned complete admission/merge policy; reference and explicit paged status/apply, bounded quarantine import/inspection, and selected-batch application through `scv db` |
| Typed indexed projections | `db_page_records.spl`, `db_page_projection.spl`, `semantic_page_store.spl` | Generation-bound row/alias/accepted/actor-counter queries and paired incremental projection updates; imported revision claims are not authoritative paged admission |
| Canonical provider follow-up | `github_binding_owner.spl` | Durable acknowledgement plus fresh scoped GET for new signed binding/common-state writes; generic producer entry rejects reserved entity kinds; historical replay reauthorizes accepted bytes |
| Retention effects | `retention_store.spl`, `retention_codec.spl`, `evidence_delete.spl` | Durable pending deletion, verified rollup/provenance, same-lease current-pin and retained-root dependency closure checks, actual unlink/absence receipts and honest resolution; bounded reference lane, not Operating B qualification |
| Authoritative paged transactions | `db_paged_*.spl`, `paged_store.spl` | Signature admission before bounded proof IO, captured-manifest indexes, unique swaps/reference counts, one authoritative SJ CAS, structural/key rotation pins and symmetric backend exclusion; execution unverified |
| Paged conflict lifecycle | `db_paged_conflicts.spl`, `paged_conflict_owner.spl` | Original signed conflict evidence in immutable pages; reviewer operation, resolution receipt and semantic/index updates share one CAS; historical replay verifies retained keys; intermediate-only conflict evidence is rejected |
| Checkpoint envelopes | `db_checkpoint.spl`, `db_checkpoint_history.spl` | Independently pinned signed Reference/Paged envelope and metadata manifests; explicit dispositions and topological history ordinals; these codecs alone do not establish complete import invariants or installation |

## Review findings addressed during coding

1. Local store paths previously followed aliases and read files without bounds.
   Reject existing directory/file aliases, stage securely, publish without
   replacement and bound HEAD/object reads. Path-based APIs still assume the
   trusted root is stable against hostile concurrent directory replacement.
2. Local snapshots previously lacked authority context. Persist a digest of
   repository, namespace, epoch and schema/reducer revisions; reopening under
   another context fails instead of silently reinterpreting rows.
3. Batch digests alone did not detect actor-counter reuse. Bind actor/counter
   to accepted digest and retained prior semantic revision; reject collisions.
4. Unknown base revisions previously passed admission. New nonreplay plans
   require a retained current/historical/genesis base.
5. A copied actor handle plus rolled-back bytes could reuse an offline UID.
   Reserve a fresh incarnation before acknowledgement and retain retirement
   evidence. This trades per-reservation files/entropy for correctness until a
   proven process-owned noncopyable counter owner exists; no scale claim follows.

## Remaining integration and execution gates

The bounded local settlement coordinator now persists original queued patches, exact candidate commits and structural policy pins; it schedules ready dependencies and reconciles uncertain publication before allocation. Local signed index observation is not protected production completion. Finish protected receipt/index recovery,
protected-authority deployment admission, cross-replica delivery admission,
paged adapter qualification, complete command coverage and resnapshot/epoch
migration orchestration. The source binding follow-up is implemented; live
provider qualification remains open. Compressed/archive
bundle formats are explicitly unsupported by the initial quarantine owner.
Admission/alias resolution, confidentiality, durable CI state, provider outbox
and local conflict lifecycle now have integrated source and focused tests; their
full requirement oracles still require execution and broader integration.

Keep broad fail-fast system scenarios until their full oracles are implemented.
Run new source tests with an admitted pure-Simple runner, then full selected
acceptance, required runtime/MCP checks, generated-manual validation, host
qualification and Operating B measurements. Do not describe later regression
execution as an earlier test-first RED/GREEN cycle.

The new authoritative path facade removes the local store's blanket Windows
rejection. Candidate, transport, external evidence/key and page owners have also
been migrated. Unsupported volume
identity queries fail closed; supported-host success tests must actually run
and succeed, not accept an unsupported result as PASS.
SJ's existing stale lease recovery and actual process crash boundaries need
separate integration evidence. The private work PR remains a draft until those
release gates are satisfied; no protected branch or release tag is updated.

## Compact alias interchange source

REQ-002 now has a strict versioned header/cell codec and three owner-integrated system test sources. A bare decimal requires its transported namespace/epoch/kind header and independently supplied expected context. Full positive u64 values are supported; overflow, zero, ambiguous decimals and mismatched contexts fail closed. This representation allocates nothing and grants no settlement authority. Execution remains unverified.

The existing command owner now exposes queue-status and queue-enqueue with independent policy pins and exact queue HEADs. Enqueue persists the original signed patch through the queue owner and reports local queue state only; it neither invokes a signer nor publishes a remote ref. Command regression source covers original bytes, replay, stale HEAD, forged signature and untouched semantic/settlement channels.

REQ-035 system source now drives actual local Git/queue admission and restricted external key lifecycle. Three additional scenarios prove authored oracles for reviewed-value publication, secret/PII sample rejection, forbidden classification and owned-key deletion with explicit copied-key/ciphertext limitations. Shared restricted fixtures are extracted unchanged from the existing integration spec. System inventory is 12 actual-owner scenarios and 141 explicit fail-fast scenarios; all remain execution-unverified.

## Streaming hydration source checkpoint

Integrated retained-handle streaming hydration and disk-backed evidence closure, plus two unit and four filesystem regression sources (including 100 MiB). Source review repaired missing Windows metadata rights and cleanup after final parent-sync failure. Windows/Linux native IO is implemented; other hosts explicitly refuse. Receipt semantics do not grant pin or deletion authority. Runtime execution, throughput/RSS, host qualification and scalable retention remain open. Checkpoint installation remains isolated pending an aggregate validation-budget repair; its history and canonical-codec review findings are resolved.

Checkpoint installation effect code is preserved in the isolated checkpoint lane through 7a90c461297 but is not integrated: independent review found missing cumulative page-read/codec-work limits and repeated Reference snapshot decoding. History-root/accepted-ancestry and canonical nested-codec fixes are present there. The shared bounded-reader repair remains unimplemented and blocks source acceptance. The paged retention authority/fencing refinement is recorded in doc/05_design/simple_distributed_textual_databases_retention_paged.md; it adds no retention implementation or deletion authorization. This bounded work cycle stops with the selected scope unfinished and PR draft.

REQ-030 hydration boundary now invokes actual 100 MiB external-envelope inspection, digest-verified streaming copy and full byte readback, with insufficient-content-quota refusal and unchanged semantic state. Shared hydration fixture functions were extracted unchanged. Inventory: 13 actual-owner system scenarios, 140 fail-fast; all execution-unverified. Git placement and timing acceptance are still open. Independent source review found no concrete blocker.

REQ-032 now has three real-filesystem local resolution source oracles covering exact/aggregated/restricted/unavailable, actual day-end rollup identity, and missing/corrupt bytes overriding unchanged catalog references. Independent source review found no concrete blocker. System inventory is 16 concrete owner scenarios and 137 fail-fast cases; runtime remains unexecuted. Historical semantic-revision query input, structured provenance, and canonical remote retention authority remain missing; these local tests do not close the full requirement.

## Follow-up runner audit after the release merge

The read-only audit during this continuation found no newly admitted full pure-Simple `test`/`check` runner. A live producer (PID 25836 at observation time) was running `native-build --entry src/app/cli/bootstrap_main.spl` under `C:/dev/simple-item1-bootstrap-export-20261003/build/bootstrap/item1-stage2-export-20261003/`. Its authority executable hash was `40c58c6cc30fdbb6650a396eeb84873e7fa1a74baea752d50c137a0f55654233`; the matching preflight artifact labels that hash as `seed_sha256`, not a full test-runner admission. The intended stage2 output directory was empty and progress remained at stage2. This observation does not establish the producer's later state.

No capability probe, bootstrap command, Rust-seed execution, or test run was performed. `bin/release` was absent in the audited main checkout. A subsequent runtime attempt requires a new output and admission/capability evidence; an unchanged seed or preflight-pass receipt is insufficient. PR #2286 was externally merged at `70b68d490a7`; this is not runtime validation. Follow-up PR #2302 contains unfinished source work and must retain those gate limitations.

## Integrated checkpoint source and bounded reader

The previously isolated same-epoch checkpoint installer, signed history/current-root checks and nested canonical encodings are integrated into the follow-up branch. The aggregate validation defect now has a source repair: explicitly threaded reader counters, verified-page caching, cached Reference indexes, captured generation/queue reuse and recovery reservations. Independent source review resolved over-reserved paged previews and under-reserved authorization; a fixture metadata admission correction and removal of an unsupported aggregate held-read claim followed. Seven new regression sources accompany the reader. The bug report records source repair with execution still unverified, not a runtime PASS.

Validation IO/work ceilings exclude independently bounded staging/import scratch effects and held publication IO; there is no whole-install bound or performance claim. History traversal remains capped at 4096 records, migration is not implemented, and production publication/cross-replica fencing/scalable retention/full system oracles remain unfinished. No admitted runner was used; mandatory runtime/core/MCP/host/crash/coverage checks remain outstanding. PR #2302 remains intended as draft source work, not release readiness.

## Binary Git object boundary

Integrated a bounded binary blob owner through the existing candidate owner's private scratch registry. Raw bytes use Git object files and bounded no-follow file reads; process stdout carries only object metadata and generated filenames. Reads enforce object format, blob type and a 16 MiB maximum before materialization. Writes use exclusive staging, exact byte readback and identity-checked cleanup. Implicit lazy fetch is disabled. The ownership marker read is bounded at 4096 bytes.

Seven regression sources cover SHA1/SHA256 binary roundtrips, zero-length blobs, quotas and non-blob objects, invalid OIDs, forged ownership, configured URL redirection and generated temporary paths. Source review confirmed the existing binary-file facade permits an empty file under a zero-byte limit. These are unexecuted Simple test sources; the earlier Git-only binary probe does not validate the Simple wrapper. Paged settlement and historical-query implementation remain isolated pending review. System inventory remains 18 actual-owner scenarios and 135 explicit fail-fast cases.

The subsequent read-only producer observation found `stage2/x86_64-pc-windows-msvc/simple.exe.rejected` and `bootstrap-progress.state` reporting `milestone=exit-2` under the same item1 stage2-export build directory. This replaces the earlier empty-output observation; it supplies no admitted runner. No rejected executable was invoked and no tests were run.

## Local paged settlement source

Integrated raw binary paged Git projection, queue v2 and the shared local settlement coordinator. The queue preserves original signed patches and exact candidate commit bytes; recovery reconciles prior publication before replanning. Readback checks signed receipts, exact trees including directory entries, page bytes and accepted-batch proofs. A private bounded in-process cache admits roots only after full import or authenticated incremental planning. Credential rotation remains distinct from structural migration. Existing reference queue v1 remains supported; backend conversion is explicitly refused.

Fourteen filesystem/bare-Git regression sources cover canonical alias allocation, exact candidate recovery, stale-head replan, revoked keys, extra tree content, empty subtrees, non-bare remote refusal, checkpoint barriers/pending preservation, dependency scheduling and SJ exclusion. Independent source review repaired hidden empty subtrees; final bare-remote checks and cleanup were reviewed. Facade guards and source whitespace passed in the owning lane. No Simple tests ran. Cold validation, invariant checks, export and recovery use separately bounded passes, not a measured aggregate resource guarantee. Protected GitHub publication, scalable retention, cross-replica fencing and Operating B qualification remain open.

PR #2302 was externally merged at head `e1d77c2ff70` into release commit `5742353e641` while these additions were being prepared. The rejected non-fast-forward push changed no remote history. The source additions were preserved on `work/item2-paged-history-20261003`, based on that release commit, in draft PR #2306. This external merge supplies no runtime acceptance evidence. Historical-query prerequisites now include a verified retained-generation read API and two regression sources; the complete query remains pending its source-review checkpoint.

PR #2306 was subsequently externally merged at head `a6f404fd3a3` (`2026-10-03T06:03:50Z`) after another session merged release changes into its branch. The next normal push was rejected without replacing remote work. The retained-generation prerequisites and later historical-query work remain local until their next reviewed integration; no further draft PR was opened during this concurrent merge activity. Neither external merge changes the UNEXECUTED runtime status.

## Historical evidence source checkpoint

Integrated the historical archive/query owner locally, after independent source review. It authenticates the captured checkpoint and reachable requested revision, verifies the actual historical semantic image, derives the evidence digest from its immutable admitted run-manifest row, and inspects the actual external object. Structured results distinguish exact, aggregated, restricted and unavailable evidence with explicit provenance. Historical Paged aliases use requested-manifest proofs; older Reference aliases without a signed historical map remain unavailable. Locator hints cannot override a valid retained-generation fallback. Manifest revisions are append-only across ordinary admission and checkpoint preservation.

Eleven new integration scenarios use real signed patches, two semantic revisions, distinct CAS bundles and actual signed checkpoint installation. They cover archived and retained-image lookup, a manifest absent at the older revision, alias context, malformed references, 100 MiB streaming, missing/corrupt/truncated envelopes, retained aggregates and zero-hop refusal, restricted bytes, cumulative quotas, generic mutation denial and Reference checkpoint rewrite refusal. Review repaired alias-context validation, an incorrect import, quota error shaping and pre-IO zero-hop handling. The owning lane's whitespace and working/staged facade checks passed; tracked generated-spec layout contained no executable specs. The merged checkpoint file retains both paged queue handling and immutable-manifest preservation.

This continuation adds 34 regression cases: 7 binary Git, 14 local paged settlement, 2 retained-generation and 11 historical-query cases. All are UNEXECUTED; no earlier RED/GREEN, coverage or runtime readiness is implied. System inventory remains 18 actual-owner sources and 135 explicit fail-fast cases. Paged historical alias/missing-page and checkpoint rewrite regressions, multi-generation rollup/key-loss cases, broader reproduction closure, migration, protected publication, scalable retention and full Operating B qualification remain open. The historical source and generation prerequisites are committed locally on `work/item2-paged-history-20261003`; they were not included in the externally merged PR #2306.

## Historical acceptance and rollup continuation

Six integrated regression sources now exercise actual three-generation rollups, missing/tampered predecessors, hop/byte limits and independent checkpoint verification keys. A fresh signed checkpoint can attest accepted rows after the original producer key is removed, while original patch replay still fails authorization; no old producer-signature proof is claimed. The restricted fixture now creates and decrypt-verifies genuine owned AEAD evidence instead of relying on a header marker. Source review also repaired its lowercase outcome precondition to the accepted `PASS` value.

REQ-032's three system scenarios now include actual signed-history queries and provenance alongside their existing local catalog/CAS checks. REQ-033's happy/boundary placeholders are replaced by actual duplicate registration, rollup publication/readback, declared histogram bins and preserved late-input generation links. Review caught and corrected a historical fixture cohort mismatch. The system inventory is now 20 actual-owner sources and 133 explicit fail-fast cases; the percentile-averaging refusal remains open. The manual and test-plan inventory track these authored sources, not executed evidence. The unchanged rejected bootstrap output supplies no admitted runner; all tests remain UNEXECUTED. Paged-history and exact configuration/reproduction admission work continue in isolated lanes.

REQ-013 now has two additional real-owner system test sources: concurrent signed edits from the same retained base merge different declared fields, while reviewed and ACL-admitted list/set writes to undeclared fields fail without changing the generation. Independent source review found no concrete blocker. Inventory: 18 actual-owner cases and 135 fail-fast; all unexecuted. The combined delete/update/scalar boundary remains open because row-level delete/update conflicts lack durable catalog evidence; the source gap is tracked separately.
