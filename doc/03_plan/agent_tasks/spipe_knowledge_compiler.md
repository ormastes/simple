<!-- codex-design -->
# SPipe Knowledge Compiler — Agent Task and Integration Plan

**Date:** 2026-08-25  
**Status:** Implementation handoff  
**Source:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`  
**Merge owner:** `/root`  
**Final reviewer:** best available normal/highest-capability model, independent of implementation lanes

## 1. Delivery contract

Implement dependency Waves 0–10 in order. A later wave may be explored in parallel, but it may not merge until every predecessor exit gate is evidenced. Wave 11 (FUSE/ProjFS) is explicitly deferred and is not required for feature completion.

The merge owner alone edits shared schemas, `.spipe/spipe_knowledge_compiler/state.md`, cross-lane indexes, integration manifests, and this plan. Agents must preserve unrelated dirty files, stage only explicit owned paths, and return commit hashes plus verification evidence. No agent may declare the feature complete; the final reviewer audits AC-1 through AC-17 plus delivery criterion DC-1 against current files and command evidence.

## 2. Interfaces frozen before fan-out

Wave 0 derives and publishes these names and versioned contracts from accepted requirements before lower-model sidecars or implementation lanes begin. It does not pre-approve architecture decisions before the requirements and threat model are complete:

- Core: `KnowledgeCompiler`, `KnowledgeSnapshot`, `KnowledgeDelta`, `ArtifactRecord`, `SectionRecord`, `TraceEdge`, `DiagnosticRecord`. `KnowledgeDelta` is the sole incremental envelope and contains ordered `ArtifactDelta`, `GraphDelta`, and `IndexDelta` payloads; those payload types are not competing top-level update protocols.
- Internal ports: `LexicalSearchPort`, `SemanticSearchPort`, `SymbolIndexPort`, and `ProjectionPort`. Core services depend only on these exact `*Port` contracts; no generic search or source-symbol port alias is part of the frozen interface.
- Provider contracts: `SearchProvider`, `SourceSymbolProvider`, and `ProjectionProvider` cover in-process, process, and server-backed implementations. Adapter mappings are explicit: every search provider is wrapped before injection; `InProcessSearchProviderAdapter` wraps the dependency-free JavaScript `SearchProvider` and satisfies `LexicalSearchPort` plus `SemanticSearchPort` only when that capability is advertised, while `SearchProviderAdapter` wraps configured process/server search providers under the same port rules. `SourceSymbolProviderAdapter` satisfies `SymbolIndexPort`, and `ProjectionProviderAdapter` satisfies `ProjectionPort`. `KnowledgeCompiler` sees only the internal ports and never a provider directly.
- Provider streaming/control contracts: `ProviderByteStreamPort`,
  `ProviderFrameDecoderV1`, `ProviderFrameEncoderV1`,
  `ProviderRequestControlPort`, `ProviderWorkMachineV1`, and
  `ProviderSessionOwnerV1`. Protocol 1.0
  remains one logical request/response per frame; only transport progress and
  bounded computation are incremental. `ProviderSessionOwnerV1` owns one active
  work machine plus exactly 16 queued ordinary requests and independently dispatches fully
  validated `cancel`/`shutdown` control frames. Protocol 1.0 requires the exact
  `cancel:true, stats:true` capability object; the current `cancel:false` or
  platform-varying `stats:false` state is red/nonconforming until production
  owners pass the matrix. Helpers or synchronous dispatch cannot promote it.
  The closed protocol-1.0 initialize schema remains byte-identical: queue,
  pending-byte, transport-timeout, work-step, and checkpoint-gap limits are
  host-local configuration/evidence, not new handshake fields. Advertising any
  such field first requires an explicit compatible protocol minor.

The six streaming interfaces have these frozen language-level operations; a
lane may add private helpers but may not rename, merge, or bypass them:

```text
ProviderByteStreamPort.read_some(maximum_bytes: i64, deadline_at_ms: i64) -> ProviderByteReadV1
ProviderByteStreamPort.write_some(bytes: [u8], offset: i64, maximum_bytes: i64, deadline_at_ms: i64) -> ProviderByteWriteV1
ProviderFrameDecoderV1.configured(limits: ProviderTransportLimitsV1) -> Result<ProviderFrameDecoderV1, text>
ProviderFrameDecoderV1.push(bytes: [u8], offset: i64, observed_at_ms: i64) -> ProviderFrameDecodeStepV1
ProviderFrameDecoderV1.take_complete() -> Result<ProviderFrameCompletionV1, text>
ProviderFrameEncoderV1.configured(payload: ProviderSegmentedBytesV1, limits: ProviderTransportLimitsV1) -> Result<ProviderFrameEncoderV1, text>
ProviderFrameEncoderV1.complete() -> bool
ProviderFrameEncoderV1.next_write(maximum_bytes: i64) -> ProviderFrameWriteLoanV1
ProviderFrameEncoderV1.advance(written_bytes: i64) -> Result<(), text>
ProviderRequestControlPort.register(request_id: text, first_header_at_ms: i64, requested_deadline_ms: i64, intent_hash: text) -> Result<ProviderRequestControlHandleV1, text>
ProviderRequestControlPort.cancel(cancel_request_id: text, target_request_id: text) -> Result<ProviderCancelResultV1, text>
ProviderRequestControlPort.try_commit_admission(request: ProviderRequestControlHandleV1, intent_hash: text) -> Result<ProviderCommitAdmissionPermitV1, text>
ProviderRequestControlPort.complete(permit: ProviderCommitAdmissionPermitV1, outcome_hash: text) -> Result<(), text>
ProviderWorkMachineV1.request_id() -> text
ProviderWorkMachineV1.step(lease: ProviderStepLeaseV1, budget: ProviderBudgetPort, checkpoint: ProviderCheckpointPort) -> ProviderWorkStepV1
ProviderSessionOwnerV1.configured(service: SpipeProviderServiceV1, control: ProviderRequestControlPort, limits: ProviderLimitContractV1, stats: ProviderProcessStatsPort) -> Result<ProviderSessionOwnerV1, text>
ProviderSessionOwnerV1.run_tick(stream: ProviderByteStreamPort) -> Result<ProviderSessionTickV1, text>
ProviderSessionOwnerV1.finished() -> bool
```

`ProviderCheckpointPort` is request-scoped: the session owner binds the
validated `ProviderRequestControlHandleV1` once at construction, and leaf work
calls only `checkpoint(progress: ProviderCheckpointProgressV1)`. No algorithm
accepts, chooses, or fabricates a request handle at a checkpoint.

The focused architecture's Section 4.1 is the normative signature authority.
Both byte results use the closed four-state status
`data | timeout | eof | error`; positive progress is `data`, while zero-byte
would-block is `timeout`, never data. Read and write each receive an absolute
transport deadline. Each decode step carries exactly one
`ProviderFrameDecodeEventV1`; its closed `kind` is `none | header | payload`.
A payload event carries one bounded immutable `ProviderFramePayloadChunkV1`
with exact `bytes`, `offset`, `count`, and `frame_payload_offset`. The chunk is
a fresh owner-created result moved to the caller, with no decoder-retained
payload alias. `declared_payload_bytes: i64?` is absent only for pre-header
`none`, and `payload: ProviderFramePayloadChunkV1?` is present only for
`payload`. Header emits once before payload, payload offsets are contiguous,
and `take_complete` returns metadata only. The decoder's payload count is the
sole framing cursor; adapters may not buffer a second whole-frame copy.
`ProviderCommitAdmissionPermitV1` binds request ID, registration generation,
and intent hash. It decides cancel/deadline eligibility only and is not a
mutation linearization point; durable candidate creation or the combined
terminal transaction remains authoritative. Work is capped so control is observed
at least every 4,096 input bytes or equivalent bounded inner-loop units.
`ProviderSessionOwnerV1.run_tick` performs bounded transport/control/work/output
progress and never hides an unbounded retry loop.

The parser maxima are also frozen here: 16 simultaneously open JSON object or
array containers, 262,144 lexical JSON tokens, and 65,536 aggregate members;
each completed object name/value pair and each completed array element counts
once. Implementations may configure stricter per-operation limits, never wider
ones. These and the queue/checkpoint limits remain host-local under protocol
1.0 as stated above.
- Mutations: `RefactorPlan`, `TransactionReceipt`, `RebalanceProposal`, `PromotionCandidate`. `RefactorPlan` is the only mutation-plan contract name.
- Protocol operations: `spipe_list`, `spipe_read`, `spipe_search`, `spipe_resolve`, `spipe_trace`, `spipe_diagnostics`.
- Phase exchange: the task/research/architecture/spec/implement/refactor/verify/ship UID input/output records used by Wave 7. Their contracts freeze in Wave 0; harness generation remains a separate Wave 9 deliverable.
- Manual flow helpers: `step("Index canonical knowledge artifacts")`, `step("Browse virtual knowledge views")`, `step("Search and trace artifacts")`, `step("Apply a transactional refactor")`, and `step("Audit tree balance and promotion candidates")`.
- Setup/checkers: `setup_spipe_knowledge_fixture`, `check_spipe_knowledge_compiler`, `check_spipe_provider_parity`, `check_spipe_refactor_recovery`, `check_spipe_virtual_view_safety`.
- Any incomplete scenario or adapter must fail fast with `assert(false)` or `fail(...)`; empty bodies, TODO passes, and inferred-only strict evidence are forbidden.

Contract changes require an ADR/design update, merge-owner approval, and coordinated consumer changes. Sidecars propose changes; they do not silently rename an interface.

## 3. Non-overlapping ownership lanes

| Lane | Exclusive implementation ownership | Published boundary | Forbidden concurrent edits |
|---|---|---|---|
| A — SPipe core | SPipe `src/core`, `src/model`, `src/storage`, `src/format`, `schema` | snapshot/delta/model/storage APIs | MCP, search, rebalance internals |
| B — Workspace/parser | SPipe `src/parser`, `src/workspace` | deterministic parse deltas and project registry | model schemas without A approval |
| C — Search core | Simple `src/lib/common/search` | canonical scoring/provider protocol | all DBFS/textual/embedded/server adapter paths |
| D — SPipe search/view/MCP | SPipe `src/search`, `src/view`, `mcp` | `spipe://` resolver and read-only protocol | canonical parser/model schemas |
| E — Database adapters | Simple textual, embedded/DBFS, server search paths | common-search adapters | common scorer internals; in Wave 4 E owns only the DBFS compatibility facade while C owns only `src/lib/common/search` |
| F — Trace/source/SSpec | SPipe `src/graph`, `src/diagnostics`; Simple provider app/symbol export | typed trace and symbol snapshot | rebalance objective |
| G — Refactor | SPipe `src/refactor` | plan/apply/rollback transaction API | arbitrary canonical writes elsewhere |
| H — Rebalance | SPipe `src/rebalance` | audit/proposal only | graph model and physical moves |
| I — Promotion/skills | SPipe `src/promote`, `src/skill`, `skill_src`, `knowledge` | reviewed promotion and generated surfaces | generated harness files by hand |
| J — Tests/guides | owned feature specs, mirrored manuals, fixtures, benchmarks, operator guide | evidence and documentation | product code except agreed test hooks |

Shared files are integrated only by `/root`. If a path is already dirty from an unknown lane, the assignee stops editing that path and reports the conflict.

## 4. Dependency waves

### Wave 0 — Requirements, baseline, threat model, and contracts

**Owners:** merge owner + audit sidecars.  
**Deliverables:** final REQ/NFR set and acceptance-to-evidence matrix; current CLI/MCP/setup/link behavior snapshots; repository and search/DB/trace inventories; path/URI/symlink/junction, authorization/cache, prompt-content, remote-provider, transaction, worktree, and linked-project threat model; benchmark corpora; linked-project and multi-worktree fixtures; extended config schema proposal; architecture decision candidates derived after requirements; startup, doctor, scan, duplicate, and search baselines. The performance baseline records fixed hardware/OS/toolchain/build mode, fixture revision and size, warm/cold procedure, sample count, latency percentiles, maximum RSS, and raw evidence location; later NFR comparisons must use the same qualified baseline or explicitly requalify a replacement. NFR-014 is selected as: on that qualified fixture and hardware, the warm elapsed wall-clock time for a one-artifact incremental graph/index update must be at least 20× cheaper than a warm full rebuild, measured by the same harness and aggregation rule. Research values such as an absolute P95 latency in milliseconds are provisional qualification candidates only; Wave 0 freezes an absolute budget only after the machine, corpus, profile, warm/cold state, and measurement method are fixed.
**Published interfaces:** all names in Section 2, serialization/versioning rules, provider capability negotiation, diagnostic-code registry, file ownership map.  
**Exit gates:** requirements are selected and stable; baseline evidence is reproducible on the recorded hardware qualification; threats have owners, mitigations, and negative-test evidence plans; SPipe/Simple ownership has no ambiguity; fixture includes missing link, dirty worktree, and visibility classes; all research decisions map to a requirement or post-requirement ADR candidate. Network HTTP and every mutating operation remain disabled until their specific threat-model gates pass.

### Wave 1 — Modularize SPipe without behavior change

**Depends on:** Wave 0. **Owners:** A with narrow B/D participation.  
**Deliverables:** thin `cli/spipe.js` and `mcp/server.js`; extracted CLI routing, config/link/doctor and protocol/transport modules; deterministic SDN/JSON result types; no new baseline Node dependency.  
**Exit gates:** existing command/setup/doctor fixtures retain behavior; on the fixed Wave 0 hardware-qualified harness, no-op `spipe doctor` elapsed wall-clock regresses by no more than 10% from baseline (using the declared sample/aggregation method), and other compatibility-command regressions are likewise no more than 10% unless explicitly waived with evidence; legacy MCP stdio still initializes; output compatibility differences are documented and approved; dispatcher files contain no new domain logic.

### Wave 2 — Schemas, identity, parsers, workspace registry

**Depends on:** Wave 1. **Owners:** A and B.  
**Deliverables:** project/artifact/section/edge/alias/view schemas; Markdown, SDN, SSpec, and source-metadata parsers; dry-run UID injection; linked-project/worktree registry; content-addressed cache and per-worktree overlay; inventory diagnostics.  
**Exit gates:** deterministic parse/round trip; duplicate UID and ambiguous alias detection; adoption moves no canonical file; dirty overlays are isolated; paths are locations, never identities.

### Wave 3 — Read-only graph and diagnostics

**Depends on:** Wave 2. **Owners:** F consuming A/B contracts.  
**Deliverables:** typed graph/query APIs; provenance-bearing link, heading, requirement, SSpec, test, and source edges; broken-link and trace-gap diagnostics; `TRC231`/`TRC232` compatibility; trace matrix.  
Lane A first publishes canonical `GraphNode`, requirement/NFR/scenario/symbol
records, non-colliding UID mappings, node+edge `GraphDelta`, and snapshot
stage/CAS/pin APIs. Lane F then owns graph/query/extraction/diagnostics and may
not redefine those shared records. Alias and mount records remain registry-owned
but have immutable graph projections as typed endpoints. `Behavior`, run, and
result nodes remain Wave 7 work.
**Exit gates:** every edge records origin/status/confidence/evidence/provenance and verified authority where strict evidence is claimed; inferred edges cannot satisfy strict policy; duplicate SS/SY/RQ/NFR UIDs fail; node and edge delta sets are disjoint; wrong base/before hashes fail; one-file incremental graph equals clean rebuild; snapshot CAS conflict and pin isolation pass; snapshots, graph roots, trace matrices, and diagnostics are deterministic.

### Wave 4 — Canonical BM25 and provider protocol

**Depends on:** Waves 2–3 contracts. **Owners:** C owns only the common search/scorer paths; D owns only the dependency-free SPipe fallback provider, `InProcessSearchProviderAdapter`, and SPipe command integration; E owns only the DBFS compatibility-facade paths for this wave.
**Deliverables:** C publishes shared documents/analyzer/corpus stats/scorer/top-k/explanations/provider protocol and exact + BM25 + graph candidate fusion using deterministic Reciprocal Rank Fusion; D implements the dependency-free fixed-point JavaScript fallback as an in-process `SearchProvider`, always wraps it with `InProcessSearchProviderAdapter` before satisfying internal search ports, and adds initial search/resolve/read commands; E migrates the DBFS scorer compatibility facade to the canonical common scorer without editing C's paths. The shared golden corpus and adapter conformance kit cross-check all three owned outputs. Remaining textual, embedded, and server database adapters consume this contract but are implemented only in Wave 10.
**Exit gates:** provider ordering/ties and RRF explanations match golden results; real document lengths are used by the DBFS path; DBFS legacy entry points preserve compatibility while producing canonical-scorer golden parity; embeddings are optional; incremental index equals clean rebuild; the adapter conformance kit is frozen for Wave 10.

#### Wave 4 streaming/deadline fan-out

The best-model/merge-owner pass freezes the interfaces above, the
`W4-SRCH-28` through `W4-SRCH-39` matrix in the system-test plan, the existing
manual flow `step("Search and trace artifacts")`, and the single system checker
`check_spipe_provider_parity` before any sidecar edits. Parallel ownership is
non-overlapping:

| Sublane | Exclusive paths | Required return | Forbidden overlap |
|---|---|---|---|
| `W4-RUNTIME-BYTE-POLL` | runtime-owner declarations/implementations plus the concrete `src/app/io` inherited-stdio adapter named by its accepted mini-design | binary-safe pollable partial read/write with absolute monotonic deadline and distinct data/would-block/deadline/EOF/error evidence on every admitted target | provider framing/session code; post-return clock checks around blocking reads; treating piped-child empty-string sentinels as authoritative status |
| `W4-PROD-STREAM` | `src/app/spipe_knowledge_provider/{byte_stream,frame_decoder,segmented_bytes,segmented_sink,encoder,request_control,work_machine,session_owner,main,wire_dispatch,wire_core,wire_types,protocol,query_clock}.spl` | one-frame incremental ingress/egress, sole canonical segmented-byte value owner, precharged bounded sink growth, first-byte timing, one-active+16 FIFO, immediate control, exact progress counters | test fixtures/specs; search/scoring internals; durable lifecycle internals except calls through their published ports |
| `W4-TEST-BYTES` | `test/fixtures/spipe_controlled_work/controlled_work_proof.spl`, `test/01_unit/app/spipe_knowledge_provider/{provider_controlled_work_import_smoke_spec,provider_streaming_limits_spec}.spl`, `examples/05_stdlib/spipe/test/fixture/wave4_search/provider_protocol_vectors.json` | W4-28–31 vectors and standalone/imported-runtime evidence | production provider code; session/fault spec; system spec/manual/checker |
| `W4-TEST-CONTROL` | `test/01_unit/app/spipe_knowledge_provider/{provider_deadline_control_spec,provider_session_owner_spec}.spl` | W4-32–36 deterministic boundary clocks plus scripted-pipe live cancel/shutdown frames, FIFO, state-digest, commit/fsync races, and partial-write faults | production provider code; byte/stat specs; system spec/manual |
| `W4-TEST-STATS` | `test/01_unit/app/spipe_knowledge_provider/provider_stats_count_explain_spec.spl` and ignored evidence root `build/test-artifacts/spipe-wave4/platform-stats/` | W4-37 positive independently recomputed statistics on every supported provider target; an unsupported target is `NOT EVIDENCE`, never `stats:false` conformance | provider implementation; other unit/system specs |
| `W4-IMPORT-ADMISSION` | `test/01_unit/compiler/import/spipe_controlled_work_import_regression_spec.spl` only in this fan-out | W4-38/39 minimal standalone-versus-imported reproduction under the same admitted Stage 4 runtime; if red, a separately planned compiler-owner fix with exact paths | all production/compiler source; provider/search/DBFS files; broad compiler cleanup; bootstrap substitution |
| `W4-SYSTEM-MERGE` | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl`, `doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md`, `doc/07_guide/app/spipe/spipe_knowledge_compiler.md`, `examples/05_stdlib/spipe/test/integration/knowledge_wave4_search_test.js`, `examples/05_stdlib/spipe/test/fixture/wave4_search/{conformance_evidence_schema,conformance_applicability}.json`, `doc/03_plan/sys_test/spipe_knowledge_compiler.md`, and `doc/03_plan/agent_tasks/spipe_knowledge_compiler.md` | merge of W4-28–39, real assertions, zero-stub manual, current operator guidance, admitted provenance, evidence hashes | product implementation/protocol vectors; accepting a sidecar's self-reported PASS |

`W4-PROD-STREAM` must publish the six interface signatures before test lanes
bind production calls. Test-only proof functions are parity oracles, not an
alternate product implementation. The import-admission lane starts only from
its exact standalone-versus-imported reproducer; it must record rather than
work around a short grammar/importer failure. Any source fix is a new
compiler-owner sublane whose plan names its exact files after the reproducer
identifies them; until then no compiler source path is shared or implicitly
authorized.

`W4-PROD-STREAM` may land the host capability and fail-closed normalization
before `W4-RUNTIME-BYTE-POLL`, but that state is explicitly partial. Current
blocking inherited-stdio calls and nonblocking piped-child helpers do not meet
the deadline/status contract. Completion requires the runtime primitive and a
concrete `app.io` adapter on the admitted runtime; provider-local externs and
blocking deadline emulation are forbidden.

Sublanes return changed paths, exact commands, exit statuses, runtime/binary
hash and Stage 4 provenance class, matrix rows exercised, and remaining red
cells. Lower-model sidecars may draft vectors or audit evidence only. `/root`
is the merge owner; a fresh best available normal/highest-capability reviewer,
independent of all implementation/test sublanes, must inspect raw fragment,
stall, cancellation, fault-injection, stats, and admission records before any
W4-28–39 PASS mark or `cancel:true` promotion. The merge owner runs each
acceptance command at most once after integration and observes the three-cycle
cap.

Wave 4S-C acceptance is evidence-specific. UTF-8 lanes must return every
single split plus deterministic mixed/random partition sequences and negative
offset/count/`offset > len` results. An invalid UTF-8 or SHA slice range must
be rejected before reading or charging bytes, producing output, or mutating
UTF-8 carry/SHA buffered or compressed content; rejection terminally latches
the exact recorded reason, and every later update/finalize call fails with
that reason. SHA lanes must return every single split for
0/1/55/56/63/64/65 bytes; 4,095/4,096/4,097/1-MiB lanes return exact
block/quantum/end-boundary partitions plus multiple deterministic fixed-seed
irregular partitions crossing SHA block boundaries. Frozen
receipt/replay/candidate/payload and domain-input preimages must flow through
their authoritative exported builders with exact digest/canonical-byte parity,
alongside injected charge/checkpoint failure with no digest publication. SHA
state owns one fixed reusable owner-local 64-word message-schedule workspace in
addition to the digest words and partial block. It remains O(1), is never
passed/returned, is not reallocated per block, and makes no zero-copy claim.
Both must show an executed post-fix PASS; static correction or source review
is insufficient. Current status is: work-control accepted and pushed;
request-control has a fresh focused PASS 9/9; UTF-8 has a fresh focused PASS
7/7; and the accepted SHA workspace optimization has 4,097-byte
full-versus-bounded parity plus a bounded cycle-3 guard-probe PASS at 1.26 s/
43,852 KiB. The full qualified 1-MiB `W4-SRCH-31` oracle remains `FAIL`; the
merge owner therefore keeps Wave 4S-C open pending SHA and integrated
production evidence.

Budget admission in this wave uses the exact
`ProviderBudgetPort.charge_all(charges: [ProviderBudgetChargeV1])` owner
operation. Multi-category growth, including sink `output_bytes` plus exact new
`logical_allocations`, is admitted as one batch: closed state, positive
amounts, known categories, checked duplicate aggregation, and every limit are
validated before any counter changes. The adversarial evidence must show a
second-category rejection and duplicate-sum overflow leave all counters
unchanged. The legacy `charge` operation is only a one-element compatibility
facade. SHA checkpoint rejection terminalizes hashing and forbids digest
publication; it does not require rollback of a compression already completed.
The accepted sink owns `segmented_bytes.spl`, while migration of the unaccepted
encoder away from its parallel segmented value remains red.

Streaming/control metrics are payload-free: lanes may retain phase, byte/member
counts, timing, stop reason, validated request ID, and approved hashes, but no
raw frame/payload, decoded private value, secret, or unauthorized artifact
content. The final reviewer rejects a green test whose diagnostic artifact
violates this evidence boundary.

### Wave 5 — Virtual resources, tools, and materialization

**Depends on:** Waves 3–4. **Owners:** D.  
**Deliverables:** authoritative `spipe://` resolver; lifecycle/feature/component/layer/matrix/trace/project/status/diagnostic projections; bounded MCP list/read/search/resolve/trace/diagnostic tools and resources; legacy stdio plus a stateless MCP 2026 HTTP implementation held disabled until its Wave 0 transport/auth/cache threat gates pass; deterministic pagination/cache hints; `.spipe/view/` materializer; editor-provider skeleton.  
**Exit gates:** model navigates without canonical paths; each artifact-representation file maps to exactly one canonical artifact UID, while directory indexes, search pages, trace matrices, diagnostics, and other aggregate outputs carry deterministic synthetic projection UIDs bound to the immutable snapshot UID and query/view parameters; writes fail closed; outputs are deterministic, paginated, and bounded; private data never receives public cache scope; unchanged materializations are not rewritten; HTTP cannot be enabled without path/auth/cache negative tests passing.

### Wave 6 — Transactional refactoring and repair

**Depends on:** Wave 5. **Owner:** G.  
**Deliverables:** artifact move/rename and section/tag/feature/component rename; reverse-reference index; hash-preconditioned plan/journal/apply/verify/rollback; raw-move recovery; cross-project checks; pre-commit/CI hooks. Mutation entry points ship disabled until the transaction, path-escape, authorization, concurrent-worktree, and rollback threat gates from Wave 0 pass.  
**Exit gates:** phase-by-phase fault injection yields valid old or new state; UID, aliases, and accepted trace survive; approved operations introduce no broken links; ambiguity fails closed; rollback restores content and graph hashes; unauthorized, stale-snapshot, and cross-root mutations fail closed before mutation can be enabled.

### Wave 7 — Full traceability and phase integration

**Depends on:** Waves 3 and 6. **Owner:** F with I/J consumers.  
**Deliverables:** stable Simple source-symbol snapshot provider; SSpec scenario/run/result nodes; advisory/standard/strict/mission-critical profiles; stale-result logic; implementation of the Wave 0-frozen phase UID input/output contracts; explained trace suggestions. Skill/harness compilation does not belong to this wave.
**Exit gates:** representative research-to-result matrices are complete; strict modes reject inferred-only evidence; trace survives physical reorganization; readable `state.md` remains while UIDs are authoritative.

### Wave 8 — Hybrid tree audit and rebalancer

**Depends on:** Waves 5 and 7. **Owner:** H.  
**Deliverables:** tree metrics; weighted graph/hyperedges; constrained Leiden-compatible communities; balanced multilevel partitioning; local refinement, hysteresis/cooldown/churn penalties; automatic virtual projection and proposal-only physical changes. Lane H owns a versioned deterministic seed derivation (`snapshot UID + scope UID + algorithm version`), fixed-point/quantized comparison precision, stable iteration/tie ordering, memory and candidate-edge budgets, and an explicit fallback path (deterministic threshold audit/proposal with no clustering) for unavailable providers or exceeded budgets.  
**Exit gates:** communities are connected; must/cannot-link and fixed roots hold; identical inputs, seed, precision, and algorithm version produce byte-identical proposals; peak memory stays within the fixed hardware-qualified Wave 0 NFR budget; provider/budget failure selects the documented deterministic fallback rather than partial clustering; unchanged runs produce no churn; each move has objective/evidence/rollback explanation; physical application requires explicit approval.

### Wave 9 — Common knowledge and skill compiler

**Depends on:** Waves 4, 7, and 8. **Owner:** I.  
**Deliverables:** two separately gated products: (1) exact/MinHash/SimHash/BM25/structural/graph/optional-semantic candidate discovery, scored review reports, family/common catalog, and provenance-preserving `extends`/override; (2) canonical skill sources and deterministic Claude/Codex/Gemini generators implementing the already-frozen phase contracts. Skill generation neither depends on nor implies approval of a promotion candidate.
**Exit gates:** promotion is never automatic; conflicts and revisions are recorded; every consumer validates; project constraints remain; generated files carry source UID/version/hash and stale outputs fail verification; skill generation passes independently when the promotion catalog is empty or disabled.

### Wave 10 — DB optimization and optional semantics

**Depends on:** Wave 4 common search/provider contract; Wave 9 is required only for optional promoted-knowledge/semantic consumers, not for core database adapters. **Owners:** E with C review.  
**Deliverables:** optimization and adapters remaining after Wave 4: textual BM25 side index; embedded index/query optimization with exhaustive/WAND paths; server segmented/Block-Max-WAND index, shard merge, capability filtering, cancellation/budgets; optional ANN/embedding providers. The already-migrated DBFS scorer compatibility facade is excluded from Wave 10 and remains a Wave 4 artifact; Wave 10 may consume it but must not re-own or rewrite its scoring contract. These adapters add textual, embedded, server, and optional semantic candidate sources to the deterministic RRF foundation already implemented and verified in Wave 4; Wave 10 neither introduces nor redefines fusion.
**Exit gates:** each DB kind proves transactional/snapshot consistency; deny-wins tests prevent field/document leakage; exhaustive and optimized top-k are identical; provider failure degrades to lexical/graph behavior; performance and RSS gates have named evidence.

### Wave 11 — OS virtual filesystem (explicitly deferred)

FUSE/ProjFS is out of the committed implementation scope. Reconsider only if measured client evidence shows MCP tools/resources, materialized views, and the editor adapter are insufficient. Any future wave requires a new ADR, threat model, invalidation design, read-only enforcement tests, and separate user approval.

## 5. Sidecar strategy and review

Lower-cost sidecars may perform bounded, read-only audits or draft fixtures after Wave 0 freezes interfaces:

- repository/current-state and compatibility inventory;
- requirements/AC/trace matrix audit;
- security, URI, worktree, and linked-project threat audit;
- search/provider/database parity fixture drafting;
- MCP pagination/cache/visibility review;
- refactor fault-injection and rebalancer adversarial fixtures;
- SSpec manual readability and guide completeness review;
- duplicate/common-knowledge candidate evaluation.

Sidecars return paths, findings, and evidence; they do not mark exclusions or done. Broad findings, generated manuals, security decisions, and acceptance marks require review by the highest-capability primary/final reviewer. `/root` resolves contradictions and owns merges.

## 6. Commit, rebase, and push checkpoints

This is a massively dirty plain-Git worktree shared with concurrent agents. Use these controls for every checkpoint:

1. Before editing, record `git status --short -- <owned paths>` and the tracked-file count (`git ls-files | wc -l`). Do not inventory or stage the whole dirty tree repeatedly.
2. Stage only explicit owned pathspecs: `git add -- <path...>`. Never use `git add -A`, `git add .`, broad globs, stash, reset, clean, or checkout to discard work.
3. Inspect `git diff --cached --name-status`; abort if any path is outside the lane. Commit one coherent, verified increment with wave/feature in the message.
4. Push at each stable wave or smaller contract-compatible checkpoint: schemas/contracts; modularization; graph; search; views/MCP; refactor; trace; rebalancer; promotion/skills; DB optimization; final guides/evidence.
5. Before synchronization, confirm no other agent owns the affected paths. Fetch and rebase linearly onto `main@origin`; do not merge. Re-check tracked-file count before/after and investigate any unexpected deletion/addition.
6. Push GitHub `main` only from the merge owner, with credential environment overrides unset as required by repository policy. A lane agent returns a commit hash and never pushes an integration branch over `main` independently.
7. If rebase conflicts touch unrelated dirty work, stop and hand the commit to `/root`; do not absorb, revert, or repair another lane's files.

“Push often” means after verified, reviewable increments—not after broken intermediates and never by sweeping unrelated dirty content into a commit.

## 7. Verification and completion ownership

Lane J maintains a requirement-to-evidence matrix covering AC-1 through AC-17 and DC-1. Each wave gets one focused verification pass; failures permit at most three distinct verify/fix cycles, and already-green unchanged checks are not rerun. Required evidence includes unit/property/integration/SSpec tests, generated manual review, provider parity, incremental-versus-clean parity, refactor fault injection, path/security isolation, rebalancer stability, promotion safety, DB authorization, latency/RSS benchmarks, runtime-facade audits, applicable compiler/lib/MCP/LSP/package smokes, and DC-1's path-scoped linear-sync/push evidence.

Final sequence:

1. `/root` integrates only reviewed path-scoped commits and updates state/evidence indexes.
2. Independent highest-capability reviewer audits every AC, exclusion, sidecar claim, generated manual, security boundary, and “done” mark against authoritative current state.
3. `/root` fixes accepted findings within the three-cycle cap.
4. Verify emits `STATUS: PASS`; documentation and guides are already current.
5. Merge owner performs the final linear rebase, tracked-file-count check, and GitHub `main` push. Release/versioning is a separate authorized step.

## 8. Active Wave 4S-C SHA blocker

`W4-SRCH-31` remains `FAIL`: cycle 2 was terminated at approximately 3:09 with
zero output after the 180-second ceiling. The accepted reusable-schedule
optimization has 4,097-byte full-versus-bounded parity; its bounded cycle-3
guard probe passed in 1.26 s at 43,852 KiB. That probe is not the qualified
1-MiB oracle and cannot close the row. No further verification cycle is
authorized in this session. See
`doc/08_tracking/bug/spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25.md`.

A later single execution of the contract-complete nine-scenario matrix after
the bounded optimization hit exactly 180 seconds and exited `124` without a
summary. The resolved release-path binary reported `Simple Language
v1.0.0-RC`, SHA-256
`3ef64bffc68d0b1c2dd851d1f02976ca98fba6f88fbb406dddf56ba7f3ca27c0`, while
its wrapper identified Rust-bootstrap-seed provenance; it is not admitted
Stage 4 evidence. `/usr/bin/time` was terminated, so RSS is unavailable. Keep
this result distinct from the earlier approximately 3:09 uncontrolled run.
Static high-capability matrix review is complete, but no candidate matrix files
are accepted and `W4-SRCH-31` remains `FAIL`.

The next assigned remediation must either add bounded stage-level progress
receipts or supply a provenance-qualified pure-Simple Stage 4 executable for
the unchanged matrix. It must not rerun unchanged, weaken 180 seconds, shrink
the 1-MiB oracle, claim ten scenarios, claim Stage 4, or borrow an RSS value
from the bounded probe.
