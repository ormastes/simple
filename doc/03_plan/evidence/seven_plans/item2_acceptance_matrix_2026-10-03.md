# Item 2 concrete acceptance matrix

Date: 2026-10-03. Baseline: release/1.0 at `e9cd3153c881c55f59eaaa2573b4b8a5e803023a`.
Selected scope remains Authority A / Adapters A / Operating B / Retention A.

This is a test contract, not a passing receipt. Every full requirement below is **UNPROVED; execution blocked**. The 153 existing executable happy/boundary/failure cases retain explicit fail-fast checks. New pure candidate-map cases call production code but remain unexecuted and do not establish disk atomicity, replica identity generation, protected publication, or recovery. No source inventory counts as runtime evidence. See the [execution report](item2_dev_execution_2026-10-03.md) for the runtime blocker and remaining gates.

## Shared deterministic fixtures and ownership

`setup_item2_uid(counter)` constructs namespace `11111111111111111111111111111111`, kind `bug`, actor `aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa`, and a positive counter. `setup_item2_two_clones` is a proposed durable fixture, not an implemented helper: private bare remote R, clones A/B at H0, epoch 1, empty allocator, separately persisted actor incarnations, signed authorized batches P/Q, and controlled clock day 0. H0/H1 denote actual captured object IDs, never invented hashes. Each durable test reopens its store in a fresh process and reads the authority again.

Existing exported identity/map and Git capability interfaces remain unchanged. Future checker helpers use `check_item2_*`; existing `check_*_contract` calls remain failing until their entire oracle is implemented. L1–L10 refer to the agent task plan production owners; a proposed owner is not a claim that its module exists.

Evidence kinds: **P** pure production execution; **D** durable process/filesystem/remote execution; **L** authenticated disposable-provider execution; **M** measured production workload. All failure checks include unchanged authority head, allocator and accepted-batch registry unless a row explicitly expects a completed prior commit. Capture before/after digests, typed result, invocation trace and reopen receipt.

## Functional cases

| ID | Concrete fixture and action | Exact acceptance and failure/unchanged oracle | Production owner; required evidence |
|---|---|---|---|
| REQ-001 | A/B offline each create counter 1; restore A counter snapshot and create again | Three distinct durable UIDs after restart; restored actor rotates; same actor/counter with changed bytes rejected without publication | L1 identity generator; D |
| REQ-002 | Epoch 1 bug alias 1 and epoch 2 bug alias 1; encode/decode versioned header | Each resolves only in its own namespace/epoch/kind; bare `1` rejected; foreign header cannot resolve local record | L1 contextual references; P+D |
| REQ-003 | Bind existing ChangeIdentity C and RevisionIdentity V to alias 1; compact/replay | C/V byte-identical before/after; mismatched revision change link rejected; alias never rewrites canonical IDs | L1 identity + L9 migration; P+D |
| REQ-004 | Allocate A=1, tombstone A, allocate B=2; kill before and after persistence barrier | Forward/reverse map, high-water 2, tombstone, registry and receipt reopen all-old or all-new; next allocation 3; no reused 1 | L1 identity map + L3 durable commit; P+D |
| REQ-005 | R authority and mirror M at H0; request allocation at both; restore obsolete authority | Only R configured protected ref allocates; M read-only; unfenced old authority requires new namespace | L3 settlement authority; D+L |
| REQ-006 | Signed P with dependency D; variants invalid signature, ACL, version, missing D; empty valid batch | Valid P admitted before allocation; variants create no candidate; empty batch leaves unrelated high-water unchanged | L2 admission + L3 settlement; P+D |
| REQ-007 | P creates record/reference and allocation; inspect candidate tree and parents | Exactly parent H0; allocation, aliases, references, registry present together; partial candidate rejected | L3 candidate builder; D |
| REQ-008 | A/B fetch H0, race P/Q; lose ACK after accepting P, retry P | One initial CAS winner; loser refetches/replans; final P/Q each once, unique numbers; retry P allocates zero new IDs | L3 publisher/read-back; D+L |
| REQ-009 | Accept receipt r1 then r2; restore r1 authority and supply altered chain/epoch/high-water | Current chain restores unchanged high-water; every regression blocks next allocation with typed rejection | L3 receipt verifier; P+D |
| REQ-010 | Patch contains identity, versions, signer, provenance, dependencies, two ordered operations and preconditions | Round-trip every field and order; remove each required field independently and reject without publication | L2 patch codec; P+D |
| REQ-011 | Equivalent typed patches with reordered map insertion; Unicode delimiter data; same batch ID altered bytes | Identical canonical bytes for equivalent values; framing unambiguous; changed payload quarantined, original registry unchanged | L2 canonical codec; P+D |
| REQ-012 | Authorized P under reducer with provider/process/network probes; repeat unauthorized | Same plan and zero external calls; authorization rejection precedes planning and allocation | L2 reducer/admission; P |
| REQ-013 | Base bug title `old`, status `open`; A title `new`, B status `closed`; then two title edits and delete/update | First merge yields `new`/`closed`; scalar and delete/update races explicit unresolved conflicts; undeclared list merge rejected | L2 schema reducer; P+D |
| REQ-014 | P depends on Q, R concurrent; feed arrival orders P/R/Q and Q/P/R | Q precedes P; concurrent ties deterministic by batch ID without inventing causality; missing Q blocks P | L2 causal planner; P+D |
| REQ-015 | Replay accepted P twice; full versus incremental rebuild; unknown schema/reducer and downgrade | State digest unchanged on replay; rebuild digests equal; incompatible versions rejected before mutation | L2 replay + L9 migration; P+D |
| REQ-016 | Persist all ten selected evidence entity kinds with revision edges and one shared run manifest | Reopen all entities/links; observations share manifest; attempt to overwrite admitted revision fails | L4 evidence store; D |
| REQ-017 | Provider run 7 attempt 1 test T digest d twice; attempt 2; altered d under attempt 1 | Counts 1 then 2; changed bytes quarantined; original attempt remains immutable | L4 identity/dedup; P+D |
| REQ-018 | Actual pass/fail under pinned pass/fail expectations; mismatch signature, infra, missing, incomplete | PASS/XFAIL/XPASS/signature mismatch/infra/NOT_RUN/INCOMPLETE/UNCLASSIFIED distinct; expectation digest never altered by ingestion | L4 classifier; P+D |
| REQ-019 | Same test under configs A/B/custom C; C fails with reproduction revision and closure | A pass/B fail/C fail coexist; C resolves exact inputs; mutable name/path/jj ID cannot stand in for revision; restricted/expired/missing explicit | L4 configuration/evidence; D |
| REQ-020 | Manifest declares shards 1/2/3; ingest 1/2, duplicate 2, retry superseding 2, then 3 | Incomplete until all declared chunks/digests reconcile; no duplicate count; skipped/missing/retried/superseded remain explicit | L4 coverage finalizer; P+D |
| REQ-021 | CI credential appends observation then attempts expectation edit, bug close, config promotion | Append accepted; three policy mutations denied and unchanged; untrusted fork cannot qualify release | L4 authorization; D+L |
| REQ-022 | Capability fixture toggles exact-head CAS, protection, read-back individually; stale H0 versus network failure | Allocation disabled when any capability absent; stale-head typed separately; unsupported transport publishes nothing | L3 Git capability adapter; P+D |
| REQ-023 | Same batch and run through GitHub/Actions live, non-GitHub Git, GitLab-CI/Jenkins fixtures | Same normalized semantic result; live receipt distinct from fixture results; provider-specific common fields rejected | L6 adapters; D+L |
| REQ-024 | Run 7 attempts 1/2 delivered by event, paginated poll and bundle in reverse order | Two attempts exactly once; artifact/attestation identities retained; unknown uniqueness dimensions reject input | L6 CI normalizer; P+D |
| REQ-025 | Persist producer manifest, lose webhook; poll overlapping windows; crash before acceptance/cursor write | Manifest discoverable before ACK; missed run recovered once; cursor stays old until durable acceptance | L6 discovery; D |
| REQ-026 | Valid bundle plus traversal, symlink, device, Unicode path collision, nested bomb and executable variants | Exact quota boundaries accepted; boundary+1 rejected before checkout; no extracted path outside quarantine, no execution | L6 quarantine; D |
| REQ-027 | Commit edit+intent; provider creates issue then loses ACK; restart/retry with same causation key | One remote issue; pending/sent-unconfirmed/acknowledged durable; changed replay quarantined; ambiguous effect retained for read-back | L5 lifecycle bridge; D+L |
| REQ-028 | Last common title `old`; one-sided then two-sided edits; HTTP permission denial versus confirmed deletion | One-sided merge accepted; two-sided conflict preserved; denial never tombstones; mirrored causation emits no loop | L5 bridge merge; P+D+L |
| REQ-029 | SJ mutation persists intent; pause provider response; second writer attempts mutation; inject lease failure | Network-start events while lease-held = 0; second writer never overlaps first commit; wait occurs after release; failed lease changes nothing | L3 SJ + L5 bridge; D |
| REQ-030 | Ingest 100 MiB raw bundle and small semantic manifest; inspect reachable Git objects and controlled CAS | Git retains semantics only; hydrate bytes match digest; accidental raw-Git candidate rejected | L7 placement/CAS; D |
| REQ-031 | Routine day 0 observation, unresolved/release pin, pending offline P; advance day 28 then 29 | Exact routine bytes available through 28 days; older routine rollup versioned; all pin closure and unsynchronized P preserved | L7 retention; D |
| REQ-032 | Query exact, rolled-up, access-restricted and removed CAS evidence | Four distinct availability results; aggregate never claims exact revision; manifest without bytes returns unavailable | L7 resolver; P+D |
| REQ-033 | Duplicate observations and two skewed daily timing cohorts; add late observation | Counts deduped; global percentile uses merged sketch; provenance/revision changes for late input; average of daily p95 rejected | L7 rollup; P+D |
| REQ-034 | A offline 45 days with update to B-deleted record and pending new record; receive complete snapshot | No resurrection; obsolete base returns ResnapshotRequired; alias/high-water/tombstone/merge/batch/history retained; pending work rebased, not dropped | L7 resnapshot + L9 migration; D |
| REQ-035 | Secret token/PII metadata and restricted CAS object; request ingestion then erasure | Default-deny fields absent from Git; controlled key deletion confirmed; report honestly identifies immutable/uncontrolled copies | L7 security/erasure; D |
| REQ-036 | Run same operation log on Linux/macOS/Windows/FreeBSD through declared capability adapters | Same semantic digest; unsupported capability typed and unchanged; no app-level OS fork/raw-runtime fallback | L9 orchestration/HAL; P+D |

## Nonfunctional cases

All measurements require three runs on the declared reference machine. Missing runtime, machine, or raw receipt means unverified, never PASS.

| ID | Concrete fixture and action | Exact acceptance and failure/unchanged oracle | Production owner; required evidence |
|---|---|---|---|
| NFR-001 | Validate receipt then remove each required field | Generator/digest, host/OS/fs/tools/Git/jj/object-format, cold/warm, warmup/samples/percentile method, command/timeout/raw paths complete; incomplete claim rejected | L10 receipt validator; M |
| NFR-002 | Generate 1,000,000 aliases + 1,000,000 observations and 10,000 import records with conflicts/tombstones/providers/artifacts/cohorts | Reopen exact counts and representative category counts; smaller corpus cannot qualify Operating B | L10 corpus + L1/L4; D+M |
| NFR-003 | Warm indexed corpus; time alias/status/dedup queries with fixed sample list | Alias/status p95 <=100 ms, dedup p95 <=250 ms; report p50/p95/p99; missing index/warm definition invalidates claim | L1/L4 queries; M |
| NFR-004 | Import 10,000 including decode/auth/reference/dedup/patch work, exclude provider transfer | <=5 s and <=256 MiB max RSS; count and digest match expected import; dropping validation invalidates receipt | L4 import; M |
| NFR-005 | Dry-run compaction of 1,000,000 rows; rebase 10,000 operations | <=10 s/512 MiB compaction, <=60 s rebase; dry-run state unchanged; all pending operations accounted | L7 maintenance; M |
| NFR-006 | Kill settlement process and restore canonical remote; fill configured pending queue while unreachable | Reachable-dependency RTO <600 s; explicit backpressure at bound; oldest accepted pending batch preserved | L3 recovery + L5 queue; D+M |
| NFR-007 | Clock at day 28 inclusive then older; query bytes and daily summary | At least 28 days exact; summary has reducer/aggregation versions + provenance; missing bytes before boundary fails | L7 retention; D |
| NFR-008 | Pin unresolved/release closure before provider expiry; hydrate 100 MiB locally; remove one dependency | 100% digest closure and <=5 s excluding transfer; removed dependency blocks closure claim | L7 CAS; D+M |
| NFR-009 | Reproducible ten-year Operating-B semantic history; pack and full clone | Each <=2 GiB; external CAS separately counted; shallow clone or omitted reachable history cannot qualify | L7 storage + L10 workload; M |
| NFR-010 | Compound race/crash/replay/tombstone/permission/secret campaign | Zero ID reuse/resurrection/inflation/lost ACKed batch/escalation/secret fields; 100% accepted reference/receipt/archive closure | L8 all production owners; D+L |
| NFR-011 | Two versioned algorithms, rotate/revoke key, replay into other repository/namespace/epoch/provider | Recorded algorithm/version and domain separation; revoked/cross-domain replay denied without publication | L2 crypto admission; P+D |
| NFR-012 | Untrusted job probes publisher credential; valid transport attempts unauthorized operation | Scoped credential inaccessible; unauthorized operation denied despite authenticated transport; logs contain no credential | L6 credential boundary; D+L |
| NFR-013 | Independently inject capability/version/ancestry/high-water/encoding/quota/remote-effect faults | Typed failure for every class; no settled publication; ambiguous remote success resolves by read-back rather than reallocation | L8 cross-layer; P+D |
| NFR-014 | Fixed ordered log under full/incremental materialization on each supported host | Identical canonical state/tree digests; mismatch fails host qualification | L2 materializer; P+D |
| NFR-015 | Core dependency graph and instrumented execution; same adapter fixtures on each provider | No provider/process/network/OS/raw-runtime core dependency or invocation; equivalent capability outcomes; scan alone insufficient | L2 core + L6 adapters; P+D |

## Compound durable campaigns and TDD order

1. **C1 two-clone offline edit:** initialize A/B at H0; disconnect; edit distinct fields; reconnect; settle both; restart both and compare canonical digests. Repeat same-field and delete/update conflicts. Covers REQ-001/008/013/014/015.
2. **C2 interruption/retry:** inject process termination before candidate persistence, before CAS, after CAS before ACK, and after ACK before local receipt. Reopen, read authority and retry identical batch. Each accepted batch exists exactly once, no allocated number is reused, and no partial state is exposed. Covers REQ-004/007/008/009/027 and NFR-006/010.
3. **C3 recovery:** keep A offline 45 days while B settles deletion and retention; resnapshot A with pending edit/new record. Preserve pending work and tombstone knowledge; stale edit cannot resurrect. Covers REQ-031/034 and NFR-007.
4. **C4 SJ lease:** instrument actual lease acquire/release, durable intent and provider invocation; block provider while another mutation progresses. Assert `network_start && lease_held` count zero and writer overlap zero. Failure to release lease cannot be disguised by a fake-provider-only result. Covers REQ-029.
5. **C5 host parity:** run identical compiled fixture/log on Linux, macOS, Windows and FreeBSD, recording filesystem and HAL capabilities. Unsupported host stays unverified; pure tests cannot qualify platform durability. Covers REQ-036/NFR-014/015.

For each campaign: first capture a real failing execution, implement its production owner, then run the same assertion once against the changed candidate. Never replace a durable oracle with a constant, skip, pure substitute or existence check. A maximum of three fix/verify cycles applies. Root owns runtime discovery and final integrated verification; sidecars do not start competing bootstrap builds.

## Additive transport TDD contract (REQ-008/022 prerequisite)

Frozen interface: `db_git_settlement_reconcile_history(source, remote, expected_old_oid, candidate_oid, scratch_parent) -> DbGitSettlementReadback`. Existing `db_git_settlement_reconcile` remains conservative. These cases prove transport ancestry only: a `published` result does not prove signed batch acceptance, registry/receipt closure or SJ orchestration. The source checkout and its Git common directory must have identical pre/post manifests; capture remote-fetch effects only in a securely created external bare scratch repository and verify cleanup.

| Case | Fixture/action | Exact oracle |
|---|---|---|
| T1 published ancestor | H0 -> candidate C -> remote H2, C sole parent H0; reconcile H0/C | `published`, observed head H2; no source/common-dir writes |
| T2 competing branch | Remote H0 -> D -> H2, candidate C absent; walk reaches H0 | `not_published`, observed head H2; no guessed acceptance |
| T3 wrong parent | C present but parent differs from expected H0; separately encounter a merge during history traversal | Wrong candidate parent: `SCVDB_PARENT_MISMATCH`; merge in traversed history: `SCVDB_HISTORY_REQUIRED`; never `published` |
| T4 moving authority | First authority read H2; advance remote before final read to H3 | `SCVDB_READBACK_MOVED`; caller retries from newly fetched head; no allocation here |
| T5 history bound | Candidate/expected-old not found within 32 cursor inspections after depth-33 fetch | `SCVDB_HISTORY_REQUIRED`; bounded walk; never infer absence beyond inspected range; transfer/storage bounds require separate proof |
| T6 invalid scratch scope | Scratch inside source/common-dir, alias escape, unsupported secure path resolution | `SCVDB_SCRATCH_SCOPE`; no scratch or source mutation; Windows capability rejection stays explicit |
| T7 missing history | Fetch object unavailable; separately inspect malformed/unreadable fetched parent record | Fetch failure: `SCVDB_READBACK_UNAVAILABLE`; unreadable fetched history: `SCVDB_HISTORY_REQUIRED`; scratch cleaned; source unchanged |

All seven cases remain unexecuted in this lane. Root and transport owner own the actual focused integration specs and runtime evidence. Windows safe capability rejection is not Windows durable feature qualification.
