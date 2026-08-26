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

The Wave 4S-C JSON interface is also frozen before implementation fan-out.
`ProviderCanonicalJsonDecoderV1.push` consumes a reported prefix and creates at
most one owned pending event; the caller must move it through `next_event`
before more bytes can be consumed. Events use only `start_object`,
`end_object`, `start_array`, `end_array`, `key`, `string`, `integer`,
`boolean`, and `null`, with exact half-open payload spans and nullable fields
whose validity is kind-specific. Container depth counts open containers (root
container one; primitive root zero), while aggregate membership counts a
completed object pair or array element exactly once and excludes the root.
The canonical decoder accepts a primitive root, but the envelope builder
requires the protocol object. Strings/keys must already be UCD-17.0.0 NFC;
keys are strictly increasing by unsigned UTF-8 bytes. The exact escape table,
single raw-byte/SHA cursor, terminal failure/finish rules, and five result
fields are normative in the focused architecture/detail design and cannot be
replaced by a queued-event or whole-tree decoder.
The focused oracle must include primitive-plus-closer two-prefix behavior,
trailing-comma rejection for `[1,]` and `{"a":1,}`, and duplicate-empty-key
rejection for `{"":1,"":2}`; none may be hidden by an empty-string sentinel,
queued double emission, or `event_queue_full`.

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
| `W4-PROD-STREAM` | `src/app/spipe_knowledge_provider/{byte_stream,frame_decoder,segmented_bytes,segmented_sink,response_plan,encoder,request_control,work_machine,session_owner,main,wire_dispatch,wire_core,wire_types,protocol,query_clock}.spl` | one-frame incremental ingress/egress, sole canonical segmented-byte and response-plan owners, precharged bounded sink growth, first-byte timing, one-active+16 FIFO, immediate control, exact progress counters | test fixtures/specs; search/scoring internals; durable lifecycle internals except calls through their published ports |
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

Canonical JSON implementation is **in progress**. Existing source is not a
PASS claim until it matches the frozen single-pending-event contract, nullable
field validity, exact spans/NFC/key ordering/escape rules, primitive-root and
member/depth accounting, one SHA/cursor, and terminal API behavior, and the
focused cases execute post-fix. This status does not change or supersede the
SHA evidence paragraph above.

Canonical response emission is also **in progress** and is a separate
acceptance unit. `response_plan.spl` solely owns a flat immutable typed
instruction tape capped at 262,144 instructions. Each step consumes at most
256 instructions and emits at most 4,096 bytes, subject to stricter configured
limits. Typed schema builders must
prevalidate final field order, ordered NFC UTF-8 keys, duplicate keys, safe
integers, and operation limits. The emitter owns the only cursor and returns
only `continue`, `ready`, or `failed`; maps, `any`, raw fragments, recursion,
joins, and staging beyond `maximum_output_bytes` are forbidden. Each accepted
chunk must be appended and hashed from the identical slice before checkpoint.
A sink/SHA/budget/checkpoint fault terminally latches, makes partial sink/hash
state unpublishable and discarded, and forbids retry/take/digest. Only `ready`
permits one take and digest. This contract makes no rollback or zero-copy
claim, and it does not change decoder or SHA evidence status.

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
**Deliverables:** optimization and adapters remaining after Wave 4: textual BM25 side index; embedded index/query optimization with exhaustive/WAND paths; server segmented/Block-Max-WAND index, shard merge, capability filtering, cancellation/budgets; optional ANN/embedding providers. The checked common scorer is an accepted Wave 4 foundation, but the DBFS compatibility facade and deterministic RRF implementation are still open Wave 4 work. Wave 10 consumes their eventual accepted contracts and must not redefine common scoring or fusion. Until those Wave 4 gates pass, Wave 10 database adapters cannot claim canonical scorer/fusion parity.
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

## 9. Active canonical-JSON decoder handoff

The latest fresh focused verification cycles reported `2/5`, `1/8`, and
`7/8`. The remaining executed failure is invalid nested-test chaining at
`.unwrap().bytes()`. No candidate decoder, focused test, or dependency file is
accepted, and the lane remains `IN PROGRESS`.

The next owner must, in a fresh session: (1) bind the nested `unwrap()` value to
an import-safe local before calling `bytes()`; (2) run the unchanged eight-case
focused spec once; (3) on a complete PASS only, request highest-capability
review proving validation precedes SHA/raw-cursor advancement and one atomic
multi-category reservation precedes stack/root/event mutation; and (4) return
separate scoped acceptance for the decoder/spec and for the currently
unaccepted `streaming_sha256` `Result`-wrapper dependency. A source-only fix or
partial result must not advance Wave 4S-C status.

## 10. Active canonical-response-emitter handoff

The emitter lane remains `IN PROGRESS`. Cycle 1 failed to parse and was
mechanically corrected. Cycle 2 then reported `5/5` for the pre-ownership
draft, but highest-capability review returned structural `FAIL`, so neither
that apparent PASS nor its source/spec is accepted. The redesign makes the
emitter own sink, SHA, budget, and checkpoint; prevalidates forged plans and
the exact output size; finalizes SHA before `ready`; and permits exactly one
take only from `ready`.

Cycle 3 executed `0/5` because a nested `.bytes()` expression is unsupported by
the current compiler. It was mechanically split through an import-safe local
after the run, but the correction is unexecuted. No emitter source or spec is
accepted. The next owner must run the unchanged focused five-case spec once in
a fresh session and, on a complete PASS only, request highest-capability
call-graph review of the redesigned ownership/prevalidation/finalization/
publication boundary. Decoder remains `7/8`; SHA remains `W4-SRCH-31 FAIL`.

### 10.1 Current evidence supersession

The decoder's final permitted cycle 3 subsequently ran `PASS 8/8`, but highest-
capability review returned `FAIL`: `transport_bytes` is a second cursor, and an
incomplete C2 prefix reports consumed/transport advance while raw/SHA lag.
That violates one authoritative raw cursor and exact consumed-prefix hashing.
Improved value-semantic rollback does not admit its source/spec.

Emitter cycles then ran `2/5`, `2/5`, and `4/5`; a post-cap second-take fix is
unexecuted. High review remains `FAIL` because exact predicted-size validation
is absent, scratch cursor state mutates before sink/SHA/checkpoint acceptance,
and first/middle/final plus cap-boundary fault cases are missing. Accept no
decoder/emitter source or spec; keep the lane `IN PROGRESS` and
`W4-SRCH-31 FAIL` unchanged.

### 10.2 V2 closure handoff

Decoder v2 ran `PASS 8/8` three times. Preserve its structurally sound central
single cursor and trial transition, but accept no files: final high review is
`FAIL` because escape assertions are length-only, token/member boundaries are
seeded rather than cumulative, all failure classes do not prove stable
`push`/`next_event`/`finish` terminal behavior, and evidence is bootstrap-seed.

Emitter v2 ran `1/8`, `8/8`, then `11/11`. Preserve the repaired trial cursor,
child-copy, exact-size/cap/fault mechanics, and member-close behavior, but
accept no files. Final high review is `FAIL`: enforce an immutable global
ceiling `<= 1,048,576`; fix payload/page/explanation maxima at
1,048,576/524,288/65,536 rather than caller input; and remove exported
generic/raw construction paths that bypass typed builders. Its evidence is also
bootstrap-seed. Overall remains `IN PROGRESS`; `W4-SRCH-31 FAIL` is unchanged.

### 10.3 Wave 4 Lane C checked-BM25 checkpoint

Commit `2b9f25f8604` accepts exactly
`src/lib/common/search/ranking.spl` and
`test/01_unit/lib/common/search/ranking_spec.spl`. Highest-capability review is
`PASS`; clean integration evidence reports source check `PASS` and focused
specification `PASS 30/30`. The evidence runtime is bootstrap-seed/non-Stage-4,
so this closes only the owned Lane C scorer slice, not Stage 4 qualification or
Wave 4.

Reject the DBFS candidate bundle as `FAIL`/`NOT-EVIDENCE`: its standalone
`wave4_compatibility` module duplicates a fixture scorer instead of adapting
the canonical scorer, its probe cells are weak, its clean/parity claim was not
executed and is false, embeddings zero-use is absent, and its capability and
statistics contracts are defective. Accept none of its files.

Lane E's next bounded task is to build the actual DBFS compatibility facade
over the canonical scorer and prove idempotent remove/re-add statistics,
deduplicated queries, honest `explain:false` until explanation exists, and
parity with an independently rebuilt final corpus. A clean post-push lint
attempt failed before a lint result at unresolved `Array.sort_by` runtime/codegen
dispatch. Treat that bootstrap-seed result as a tooling blocker, not scorer
evidence or scorer failure; do not claim a duplicate-check run. Overall Wave 4
remains `IN PROGRESS`.

### 10.4 DBFS facade attempt closure

The clean-clone candidate owned exactly the four FTS sources
`src/lib/nogc_sync_mut/db/dbfs_engine/fts/{__init__,bm25,inverted_index,search}.spl`
and the new focused
`test/02_integration/storage/dbfs/fts_canonical_facade_spec.spl`.

The three permitted cycles reached zero owned-code execution. Stage 3 Simple
hash
`9ce412a1d102de421de6d7042d8dc5c65201cc514b463b9b6a5bc5de2f66970c`
lacks `check`/`test`; Rust seed hash
`c9c783b8568cf9a199945fe1ee98d08615b728387e6c89cbdc9b50e600f3e091`
failed first on unrelated `nogc_async_mut/path.spl` `E1002 unsafe` and
`plan_sdn.spl` `Dedent`.

Static highest-capability review is `FAIL`; admissible files are `[]`.
Nested index/engine collection and struct mutations lack complete trial-copy
plus single owner reassignment, and lexical state commits before trigram/content
state. Correct the frozen `contains_document` `me fn` ABI. Expand the spec
to assert intermediate statistics and averages, full independently rebuilt
clean statistics, contains/absent behavior, exact order equality, legacy
success, and checked-upsert failure/no-change.

Keep the facade direction and focused fixture as unaccepted salvage only. The
next bounded Lane E task is value-semantic child-copy/writeback, one atomic
engine transaction, ABI repair, and the complete oracle, followed by fresh
bounded execution on a capable pure-Simple runtime. Wave 4 remains
`IN PROGRESS`.

### 10.5 Analyzer V1 contract and ownership freeze

The common batch seam is distinct from, and requires adapter parity with, the
unchanged provider streaming seam. Exact types are
`SearchFieldIdentityV1(Identifier|Title|Heading|Classification|Body)`;
`AnalyzerErrorV1(InvalidLimits|InvalidFieldIdentity|InputLimitExceeded|
InvalidUtf8|NormalizedLimitExceeded|TokenBytesLimitExceeded|
TokenCountLimitExceeded|DistinctTermLimitExceeded)`;
`AnalyzerIdentityV1` with eleven text fields
`analyzer_id,unicode_version,unicode_manifest_sha256,normalization_id,
lowercase_id,tokenizer_id,stop_words_id,stop_words_sha256,stemming_id,
field_schema_id,limits_schema_id`; and `AnalyzerLimitsV1` with five i64 fields
`max_input_bytes,max_normalized_bytes,max_token_bytes,max_tokens,
max_distinct_terms`.

Results are `AnalyzedTokenV1(value:text,position:i64,exact_identifier:bool)`,
`AnalyzedTextV1(normalized:text,tokens:[AnalyzedTokenV1])`,
`AnalyzedQueryTermV1(value:text,qtf:i64)`, and
`AnalyzedQueryV1(normalized:text,terms:[AnalyzedQueryTermV1])`. Functions are
`analyze_field_v1(text,SearchFieldIdentityV1,AnalyzerIdentityV1,
AnalyzerLimitsV1)->Result<AnalyzedTextV1,AnalyzerErrorV1>`,
`analyze_query_v1(text,AnalyzerIdentityV1,AnalyzerLimitsV1)
->Result<AnalyzedQueryV1,AnalyzerErrorV1>`, and
`unsigned_utf8_less(text,text)->bool`.

Semantics are UCD17 NFC -> default lowercase, not folding -> NFC; maximal
`Alphabetic|Decimal_Number|Mark|_` tokens; pre-stopword one-based positions;
fixed stopwords `[a,an,and,of,the,to]` with digest
`6f0a7c26d3d0e3d06a2fbbbeaa1843294f83c3be26baf1c04651191e011510bf`;
identifier exact full-normalized/no-trim token appended last at position zero
with deduplication; and QTF terms sorted by unsigned UTF-8 bytes.

Query limits are `4096/4096/4096/128/128` in struct order. Field input
hard-caps at 1,048,576 bytes and configured `max_tokens <= 524288`. Unicode
manifest, stopword, limits, and schema identities are cache identity. No
embedding, process, network, or locale access is allowed.

The analyzer lane owns only `src/lib/common/search/analyzer.spl` and
`test/01_unit/lib/common/search/analyzer_contract_spec.spl`;
`src/lib/common/search/__init__.spl` is merge-owned. The UCD17 generated
tables and manifest are missing from `main` and must land first. Current
analyzer status is `FAIL`, admissible `[]`: its parity claim is false and
bounds are incomplete. Preserve `ProviderAnalyzerLimitsV1`,
`ProviderAnalyzedTokenV1`, `ProviderAnalyzedTokenSinkPort`, and
`ProviderStreamingAnalyzerV1` unchanged. Wave 4 remains `IN PROGRESS`.

### 10.6 Unicode 17 prerequisite attempt closure

Treat these exact paths as one indivisible 14-file bundle: generator and
license at `examples/05_stdlib/spipe/tools/unicode/`; the seven UCD 17.0.0
inputs `UnicodeData.txt,DerivedCoreProperties.txt,PropList.txt,
SpecialCasing.txt,CaseFolding.txt,CompositionExclusions.txt,
NormalizationTest.txt`; generated JavaScript and Simple tables at
`examples/05_stdlib/spipe/src/search/generated/unicode_17_0_0.js` and
`src/lib/common/search/generated/unicode_17_0_0.spl`; manifest
`examples/05_stdlib/spipe/test/fixture/wave4_search/unicode_17_0_0_manifest.json`;
and tests `examples/05_stdlib/spipe/test/unit/unicode_17_tables_test.js` and
`test/01_unit/lib/common/search/unicode_17_0_0_spec.spl`.

Preserve as unaccepted work the stable 256-CCC bounded-linear repair, O(n)
sigma-context repair, and bounded 4,096-element JavaScript chunks. JavaScript
reported `PASS 7/7` across the 20,034-by-five NFC corpus, every scalar, and
1 MiB.

Do not accept the bundle. Cycle 2's Rust-seed Simple run timed out
`124` without a summary; cycle 3 repeated the same green JavaScript check,
which is neither new evidence nor compliant process. Highest-capability review
is `FAIL`, admissible `[]`: Simple push/value semantics and optimizer bounds
are unproved; the spec bypasses the file facade with `rt_file_read_text`;
`REQ-SPK-SEARCH-UNICODE-001` is orphaned; generated JavaScript names the wrong
license path; and independent lowercase coverage is weak for
`Case_Ignorable` final-sigma contexts.

Next session fixes all static defects first and then runs one bounded full
parity check on a capable pure-Simple runtime. No code is accepted, the
analyzer prerequisite is still missing, and Wave 4 remains `IN PROGRESS`.

### 10.7 Raw JavaScript RRF admission

The initial rejected candidate remains historical `NOT-EVIDENCE`. A fresh
scoped implementation repaired once-only input normalization, closed descriptor
validation, phase-specific errors, and adversarial/default/boundary coverage.
Static and final highest-capability reviews passed; syntax passed; the focused
suite passed 16/16 in cycle 2. The exact two-file raw kernel is accepted and
pushed as `595ba6e449`.

Do not expand its claim: it advances only the raw-fusion portion of
REQ-SPKC-012/013. AC-4 still requires exact identity dominance, accepted graph
candidate production/proximity, bounded adjustments, and integrated
stale/deprecated explanations.

### 10.8 Authority-bound RRF reranker admission

The dependency-free page-local reranker is accepted and pushed as
`44e65a6713`. It binds raw-fusion and evidence digests to one verified receipt,
validates the raw page defensively, preserves raw explanations, and applies the
fixed integer adjustment policy. Evidence is syntax `PASS`, focused `13/13`,
full SPipe suite `PASS`, and independent pre-runtime/final high reviews `PASS`.

The next owner must not call this global top-k evidence. Integrated search must
produce the full authorized candidate pool, apply upstream exact identity
dominance and graph candidate construction, rerank the attested page, and only
then apply the user result limit. AC-4 remains open until that pipeline and its
explanations are verified end to end.

### 10.9 Complete-pool RRF v2 admission

The additive v2 fusion/rerank prerequisite is accepted and pushed as
`32574ab884`. It preserves v1, requires complete source/count/digest envelopes,
returns the declared complete, digest-bound union up to 3,000, reranks the complete pool, and
only then applies the public 1,000-hit cap. Syntax, focused 38/38, full package,
and independent highest-capability gates passed; the rank-1,001 promotion oracle
proves premature truncation is removed.

The identity/graph orchestration owner may now depend on v2, but must bind each
source completeness digest into the search receipt, perform exact identity
dominance before fusion, fail closed on incomplete accepted-edge traversal, and
apply the user limit last. This checkpoint alone does not close AC-4.

### 10.10 Authority-bound exact identity admission

The standalone exact resolver is accepted and pushed as `d1b601697f`. It reads
one receipt-bound authorized identity projection, performs byte-exact canonical
UID lookup or unioned key/active-alias lookup, fails closed on corrupt bindings,
and prevents unauthorized identities from affecting cardinality or explanations.
Syntax, focused 8/8, full package/performance, and final highest-capability gates
passed.

The integrated search owner must consume this resolver without re-resolving or
weakening its bindings: a resolved identity is pinned ahead of retrieval and
removed from every ranked source; ambiguity is reported without a pin; not-found
continues normally. Graph/provider/RRF orchestration and AC-4 remain open.

### 10.11 Accepted graph candidate contract and evidence prerequisite

The graph candidate boundary is frozen but not implemented. It consumes one
authorization-filtered digest-bound graph snapshot, performs a fixed-count
node-authorization recheck, admits only receipt-verified accepted
explicit/generated schema-v2 edges, and runs deterministic bounded
both-direction depth-three BFS. Partial work returns only a single-use
factory-local opaque cursor; only exhaustive completion may emit an RRF-v2 graph
source and evidence digest.

The exact implementation gate enforces depth 3, sourceK 1..1000 default 1000,
page work 1..50,000 default 50,000, configurable total work 1..500,000,
20,000 nodes, 50,000 edges, 1001 roots, and
512-byte IDs. Paths repeat no node/edge; improved same-distance tuples re-expand;
the full tuple and final Artifact UID order are tested before top-K truncation.
Default and minimum/maximum boundary oracles cover sourceK/page/total work;
root-precedence oracles bind exact to `(tier=0,rank=0)` and lexical to
`(tier=1,rank=sourceRank)`.
Node authorization runs exactly once per declared node without early exit or
metadata disclosure. Cursor tests cover null-prototype/no-enumerable state,
atomic consumption, cross-factory/copy/replay rejection, partial-data absence,
hard-cap destruction, bounded state, and GC eligibility.

The lossless authority prerequisite is accepted as reranker v3 commit
`f89b120be7`: ordered `{edgeUid,authorityReceiptUid}` pairs permit one receipt to
cover multiple edges, while display arrays are derived only. Static, syntax,
focused 26/26, full package, and final highest-capability gates passed.

The graph generator is now unblocked. Do not fabricate per-edge receipts, drop
edges, or replace ordered pairs with the derived unique arrays. Graph boost and
AC-4 remain open until the standalone graph oracle and integrated search pass.
