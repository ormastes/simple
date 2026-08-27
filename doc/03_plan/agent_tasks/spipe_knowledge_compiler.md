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
- URI admission: `AuthorizationPortV1`, `CanonicalReadReceiptV1`, and
  `CursorReceiptV1`. Both receipt contracts bind authority key/epoch,
  workspace, project-or-null, `baseSnapshotUid`, `authoritySnapshotUid`,
  revision, view, normalized path and
  selector/filter digest, effective scope, ordering version, and page limit.
  The composition root alone creates the branded signed verifier and opaque
  verified grants; handlers may not use structural verifier objects, remap a
  selector, default a workspace, or authorize one workspace with another's
  receipt. `spipe://workspace/{workspace}/` is the sole workspace-root grammar.
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

#### W4A — provider-conformance closure (merge-owner sequence)

`doc/05_design/infra/spipe/spipe_knowledge_compiler_search_providers.md`
Section 13.1 is the authoritative W4A sequence.  It closes Wave 4 in this
order: (1) frozen common oracle/fixture, (2) JS in-process baseline, (3) native
Simple lexical parity, (4) long-lived framed process adapter, (5) fail-closed
same-root JS degradation, and (6) independently reviewed admission evidence.
It is not permission to broaden `bm25-fixed-v1`, reimplement RRF in Simple, or
call a micro-corpus probe a provider PASS.

The merge owner accepts a target only with a closed
`ProviderConformanceRecordV1`, recomputed fixture/root/statistics/score/
explanation evidence, the exact applicability matrix, and the security cells
applicable to its transport.  Native process work additionally requires all
streaming/control rows W4-SRCH-28–39 and a verified binary/provenance binding.
W4-SRCH-09 is separate qualified performance evidence; lack of that receipt
keeps NFR performance open even if functional conformance succeeds.  Wave 10
adapts PureDatabase, textual DB, and server DB through the frozen contract;
it must not reopen the completed Wave-4 DBFS scorer/facade migration.

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
**Exit gates:** model navigates without canonical paths; each artifact-representation file maps to exactly one canonical artifact UID, while directory indexes, search pages, trace matrices, diagnostics, and other aggregate outputs carry deterministic synthetic projection UIDs bound to immutable snapshot identity and query/view parameters; writes fail closed; outputs are deterministic, paginated, and bounded; private data never receives public cache scope; unchanged materializations are not rewritten; HTTP cannot be enabled without path/auth/cache negative tests passing. A cursor must be a signed receipt whose authority/base-snapshot/authority-snapshot/revision/view/selector/scope/page-limit bindings match the independently authorized request exactly; legacy aliases cannot remap foreign workspaces; every verifier is an admitted branded `AuthorizationPortV1`; and the positive plus hostile URI/receipt/cursor/public-error matrix in the system-test plan must pass.

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

### 10.12 Authority-bound lexical source admission and exact next ownership

The lexical source product/oracle pair is accepted at `9eb667e23b`:

- `examples/05_stdlib/spipe/src/search/lexical_source.js`
- `examples/05_stdlib/spipe/test/unit/search_lexical_source_test.js`

It captures exactly `verifySearchReceipt`, `readLexicalProviderPage`,
`authorizeArtifactCandidate`, and `verifyLexicalEvidence`; validates the full
cursor/page/receipt chain; authorizes every candidate exactly once; and verifies
the complete page-set plus ordered-rank evidence once. Its restricted
`spipe-canonical-json-v1` evidence uses NFC, unsigned UTF-8 key order, and long
lowercase C0 escapes including U+0009 as `\u0009`.

The accepted design delta is mandatory: a provider removes
`excludedDocumentUid` before ranking and pagination and its page/aggregate
receipts attest that choice. Client post-filter is not conforming because a
provider-capped 1,000-row page cannot still prove 1,000 remaining lexical rows.
The provider adapter/protocol ownership and filenames remain unfrozen; freeze
them and the independent conformance oracle before implementation. Require
`spipe-search-provider/1.0`, analyzer/score identity, exclusion, cursor, page,
and receipt parity.

Evidence is focused `16/16`; full `158/158` unit, Wave 2 `9/9`, Wave 3 `25/25`,
Wave 4 `9/9`, legacy, security, workflows, and performance `PASS`; independent
highest-capability review `PASS`.

Do not admit `/tmp/spkc-graph-candidates-4OKnKd`. It stopped at cycle cap with
focused `13/14` because its cyclic-graph `workUnits <= 9` expectation is not a
contracted oracle. All seven reported static defects were patched, but no full
suite or final highest-capability review followed. There is no commit and no AC
claim.

Remaining work uses these exact, non-overlapping pairs in order:

1. graph: `examples/05_stdlib/spipe/src/search/graph_candidates.js` and
   `examples/05_stdlib/spipe/test/unit/search_graph_candidates_test.js`;
2. provider adapter/protocol: merge owner first freezes interfaces, filenames,
   ownership, and a separate conformance oracle; no implementation starts from
   guessed filenames;
3. rerank evidence: `examples/05_stdlib/spipe/src/search/rerank_evidence.js` and
   `examples/05_stdlib/spipe/test/unit/search_rerank_evidence_test.js`;
4. pipeline: `examples/05_stdlib/spipe/src/search/pipeline.js` and
   `examples/05_stdlib/spipe/test/unit/search_pipeline_test.js`.

The rerank-evidence pair is a standalone prerequisite, not pipeline-owned test
scaffolding. The pipeline integrates only accepted exact identity, lexical and
graph sources, complete RRF-v2, rerank evidence, and pair-based reranker in that
order, with user limit last. Merge owner remains `/root`; final reviewer is the
best available normal/highest-capability model. AC-4 stays open.

### 10.13 Graph admission, provider contract freeze, and active next lane

The fresh graph admission supersedes the rejected attempt's status but not its
record. Commit `626b3e0797` contains only:

- `examples/05_stdlib/spipe/src/search/graph_candidates.js`;
- `examples/05_stdlib/spipe/test/unit/search_graph_candidates_test.js`.

Admission evidence is focused `16/16`; full unit `174/174`; Wave 2 `9/9`, Wave
3 `25/25`, Wave 4 `9/9`; legacy integration and performance `PASS`; pre-runtime
and final highest-capability review `PASS`. The cyclic oracle is exactly
`workUnits == 10`. The suite also proves hostile caps, opaque single-use cursor
lifecycle, exact continuation equivalence, total-limit destruction, exact
tuple ordering, literal digest goldens, both-direction traversal, later-better
re-expansion, and ordered edge/receipt evidence when receipts are shared.

Provider adapter ownership is now frozen. The JavaScript implementation lane
owns these exact changes:

- modify `examples/05_stdlib/spipe/src/index/contracts.js` and
  `src/index/logical_index.js`;
- modify `examples/05_stdlib/spipe/src/provider/protocol.js`, `adapter.js`,
  `js_fixed_point.js`, and `index.js`;
- add `examples/05_stdlib/spipe/src/provider/lexical_page.js`;
- add `examples/05_stdlib/spipe/test/unit/search_lexical_provider_page_test.js`;
- add
  `examples/05_stdlib/spipe/test/fixture/wave4_search/authorized_lexical_provider_page_vectors.json`.

The Simple-native mapping uses only existing owners
`src/app/spipe_knowledge_provider/{lexical,wire_query,wire_core,protocol,service}.spl`.
No new native scorer or guessed Node process adapter is authorized.

The design gate is wire 1.1 `lexical_page` plus
`authorized_lexical_page:true`, while provider/analyzer/scorer identities remain
`spipe-search-provider/1.0`, `spipe-unicode-lex-v1`, and `bm25-fixed-v1`.
Require pre-ranking exact exclusion, unchanged corpus statistics, page schema
`spipe-authorized-lexical-provider-page-v1`, adapter identity
`spipe-authorized-lexical-provider-adapter-v1`, and a cursor that binds stable
provider/query/snapshot/exclusion/rank identity but not per-page `qr-*` or
`requestedLimit`.

The conformance oracle must distinguish transport `qr-*` receipts from signed
authority `D-*` lexical-page receipts. The adapter returns a page containing
the admitted nine-field projection only after the full signed `D-*` record is
stored and re-resolved; the projection is not authority. The aggregate verifier
resolves all full authority receipts and binds page/rank/exclusion/policy/root
evidence. Protocol 1.0 is legacy-only for this path.

Execution order and ownership:

1. **Provider JS/in-process lane:** implement the frozen files and independent
   vector oracle. Do not claim native process parity.
2. **Async-boundary design lane:** decide asynchronous lexical-source v2 versus
   asynchronous collection plus immutable synchronous replay before any native
   process adapter is named.
3. **Rerank-evidence lane:** currently active; preserve its standalone product/
   oracle ownership and require a separate admission review.
4. **Pipeline lane:** begin only after provider and rerank-evidence admission;
   integrate exact pin -> excluded lexical -> graph -> complete-pool RRF v2 ->
   evidence -> pair rerank/explanation -> user limit.

Candidate NFR gates are lazy startup, no hot process spawn/tree scan/retry
sleep, startup P95 at most 250 ms, warm 50,000-artifact lexical P95 below 100
ms, and qualified maximum-RSS evidence with a configured cap. Numeric RSS is
blocked pending Wave 0 measurement. There is no current provider conformance or
pipeline-integration claim. Merge owner remains `/root`; final acceptance owner
is the best available normal/highest-capability reviewer. AC-4 remains open.

### 10.14 Corrected provider-authority implementation lane

The nine-field-only adapter described in the preceding freeze is rejected as a
pre-authority alternative. The provider lane must implement the full
synchronous in-process ABI in detail design Section 17.7 without narrowing its
claims. The interface names are frozen before implementation fan-out:

```text
createAuthorizedLexicalProviderPageBridgeV1
  config: {providerSession,issueTransportQueryReceiptV1,
           verifyTransportQueryReceiptV1,executeLexicalPageV11,
           lexicalEvidenceAuthority,lexicalEvidenceStore,clockNowMs}
  output: {readLexicalProviderPage,verifyLexicalEvidence}

createBoundedLexicalEvidenceStoreV1
  output: {reserveOperationV1,commitReceiptV1,resolveReceiptV1,
           tombstoneOperationV1}

createInProcessLexicalPageExecutorV11
  config: {provider,providerSession,verifyTransportQueryReceiptV1,
           lexicalCursorAuthority,clockNowMs}
  output: frozen executeLexicalPageV11(envelope) -> response
```

All calls are direct synchronous calls; Promises/thenables, filesystem work,
process spawning, polling, and retry sleeps are out of scope. Semantic provider
identity stays `spipe-search-provider/1.0`; wire 1.1 adds only
`authorized_lexical_page:true` and `lexical_page`.
Initialization must preserve the exact legacy 1.0 closed capability result and
add only the final capability for an exact 1.1 request; no silent minor
selection is allowed. Canonical UIDs retain both admitted 32-hex and
26-Crockford payload spellings, and `qr-*` remains `qr-<64 lowercase hex>`.

#### Product ownership

| Lane | Exact files | Deliverable |
|---|---|---|
| Contract/index | `src/index/contracts.js`, `src/index/logical_index.js` | 1.1 capability and exact pre-ranking exclusion without corpus-stat mutation |
| Wire/session | `src/provider/protocol.js`, `src/provider/adapter.js` | closed 1.1 envelopes, full `qr-*` records, validated frozen session |
| Provider | `src/provider/js_fixed_point.js` | synchronous page execution and provider-side `qr-*` verification |
| Authority bridge | new `src/provider/lexical_page.js` | full page/aggregate records, signatures, resolution, projections |
| Evidence store | new `src/provider/lexical_evidence_store.js` | bounded atomic receipt/replay store |
| Export | `src/provider/index.js` | public factory/constants only |
| Oracle | new `test/unit/search_lexical_provider_page_test.js` | independent authority/wire/store/lifecycle tests |
| Vectors | new `test/fixture/wave4_search/authorized_lexical_provider_page_vectors.json` | literal domain/preimage/UID/signature/store goldens |

All `src/` and `test/` paths in this table are relative to
`examples/05_stdlib/spipe/`. Do not edit `provider/durable_lifecycle.js`: its
async mutation lifecycle is a different owner. Do not edit Simple-native files
or introduce a Node process adapter in this lane.

#### Required implementation sequence

1. Freeze constants, closed record validators, restricted canonical encoder,
   exact digest preimages, authenticated cursor schema, deterministic
   `lpo-/lao-/req-lp-` mappings, and independent literal vectors.
2. Add protocol 1.1 negotiation and provider/session validation while retaining
   all 1.0 semantic identities and legacy behavior.
3. Implement provider-owned exclusion before scoring/top-k/pagination; keep
   snapshot `N`, `df`, and average document length unchanged.
4. Implement and test full `spipe-query-receipt-v1` issue, provider-side check,
   exact echo, and independent bridge verification for `lexical_page`.
5. Implement the bounded store and its atomic reserve/commit/exact-replay/
   conflict/tombstone
   behavior; operation keys are exact `lpo-<64 lowercase hex>` or
   `lao-<64 lowercase hex>` values, `inputDigest` is the corresponding full
   operation digest, kinds are `lexical_page|lexical_aggregate`, and tombstone
   reasons use the seven-value enum frozen in design Section 17.7. Pre-charge
   2,048 bytes of tombstone headroom per reservation so commit-capacity failure
   cannot block cleanup.
6. Implement page operation hashing, full page `D-*` sign/self-verify/commit/
   re-resolve, then derive the existing nine-field page projection.
7. Implement aggregate resolution of every page `D-*`, re-verify every embedded
   `qr-*`, rebuild cursor/rank continuity and all digests, then sign/commit/
   re-resolve the aggregate `D-*`.
8. Prove start/end bridge and start/end provider-executor clock observations,
   canonical-byte equality of the
   complete echoed `qr-*`, expiry, authority/key/policy/revocation/root/scope/provider-generation
   drift fail closed and never trigger per-page fallback.
9. Run the focused oracle once, the full SPipe package once after focus passes,
   and the existing Wave 4/legacy/performance gates once. Stop after at most
   three verify/fix cycles.
10. Require pre-runtime and final highest-capability review before merge.

#### Admission evidence

The oracle must cover every exact input/output record and domain from design
Section 17.7, including two-sided `qr-*` verification, `qr-*`/`D-*`
non-substitutability, full stored record resolution, write/read witnesses,
aggregate reconstruction, replay/conflict/expiry/revocation, proof that replay
does not issue, execute, sign, or commit, hostile
canonicality and cap inputs, provider identity stability, no mid-stream
fallback, and literal signature/UID/digest goldens. It must also prove direct
non-thenable operation and the fixed 4,096-record/64-MiB store envelope.

Candidate performance receipts are bridge construction P95 under 5 ms,
authority/store overhead P95 under 10 ms per 1,000-hit page excluding scoring,
warm lexical P95 under 100 ms for 50,000 artifacts, startup P95 under 250 ms,
and no process/file-scan/retry activity on the hot path. No provider conformance
or AC-4 completion is claimed until product, oracle, package checks, performance
receipts, and highest-capability review all pass.

The store bound counts every reservation, active/replay row, tombstone,
operation key, and signed record inside one 4,096-entry/64-MiB generation
envelope, including each reservation's fixed 2,048-byte worst-case tombstone
headroom. Active replay tombstoning uses a null token plus the exact stored
UID/digest; reserved tombstoning uses the single-use token. Tests must cover
work crossing receipt expiry and post-commit resolve corruption.

Sidecar lanes: lower-model implementation assistance is limited to the fixed
file ownership above; no sidecar may change schemas/domains. Merge owner is
`/root`; final reviewer is the best available normal/highest-capability model.

### 10.15 Corrected handoff ledger and resume order (2026-08-26)

1. **Provider authority — contract only.** Commit `47a922eec6` passed the
   highest-capability contract review for the complete ABI in Section 10.14 and
   detail design Section 17.7. The implementation attempt in
   `/tmp/spkc-lexical-provider-z15Uhp/repo` stopped at the pre-runtime review
   cap and made no in-scope product/oracle edit. Resume in a fresh session from
   the full final ABI; do not implement the rejected minimal projection
   adapter.
2. **Rerank evidence — candidate only.** The exact untracked pair in
   `/tmp/spkc-rerank-evidence4-aIcFIZ/repo` is
   `examples/05_stdlib/spipe/src/search/rerank_evidence.js` and
   `examples/05_stdlib/spipe/test/unit/search_rerank_evidence_test.js`. It has
   no commit and is not admitted. Focused `16/16`, full unit `190/190`, Wave 2
   `9/9`, Wave 3 `25/25`, Wave 4 `9/9`, legacy, security, workflow, and
   performance gates passed, but final highest-capability review after cycle
   three found unresolved `limit_exceeded` precedence for oversized derived
   evidence arrays and an unresolved semantic-contract-string binding. Start a
   fresh exact two-file fix/review lane; do not rerun unchanged green commands.
3. **Pipeline — waiting.** Begin only after provider implementation admission
   and rerank-evidence admission. Preserve the frozen order: exact resolution,
   excluded complete lexical collection, graph generation, complete-pool RRF
   v2, authority-bound evidence, pair rerank/explanation, then user limit.

Merge owner remains `/root`; the final reviewer remains the best available
normal/highest-capability model. AC-4 remains open.

### 11.1 Wave 5a seal and alias repair (2026-08-26)

W5A-A owns a non-cyclic seal: `TargetInventoryManifestV1` binds the existing
base snapshot UID, and a separate content-addressed `AuthorityManifestV1`
authority snapshot UID commits the base UID plus inventory root. Receipts bind
the authority snapshot. The sealed inventory owns normalized legacy alias
mappings, so the frozen authority API includes
`resolveCanonicalAlias(view, alias)` before receipt verification; external
registry/path alias lookup is not admissible. W5A evidence must inject cyclic,
tampered-root, missing/ambiguous alias, and foreign-authority alias cases.

### 10.16 Superseding admission ledger and provider blocker handoff (2026-08-26)

1. **Rerank evidence — admitted.** Commit `4455b760da` admits the exact
   `src/search/rerank_evidence.js` and
   `test/unit/search_rerank_evidence_test.js` pair. Syntax passed; focused
   `18/18`, unit `192/192`, Wave 2 `9/9`, Wave 3 `25/25`, Wave 4 `9/9`, and
   legacy, security, workflow, and performance gates passed. Final independent
   xhigh review passed in cycle 2 of 3. Do not repeat these unchanged green
   gates.
2. **Provider authority ABI — stopped, not landed.** The repair lane exhausted
   the mandatory three review/fix cycles and remains `FAIL` on exactly four
   blockers: collision-result signaling, executor error classification,
   cursor error precedence, and canonical-byte accounting versus heap/RSS
   limits. It made no product edit, ran no product test, and produced no
   repository-history commit. Object `3827a1099e` in
   `/tmp/spkc-provider-abi-repair2-clean` is a failed immutable draft for
   forensic comparison only; do not copy its contract text into implementation
   or authoritative documentation.
3. **Pipeline — waiting on provider.** Keep its frozen integration order, but
   do not start it until a fresh provider ABI repair and provider implementation
   are independently admitted. Wave 4 and AC-4 remain open.

Merge owner remains `/root`; final acceptance remains owned by an independent
normal/highest-capability reviewer.

### Wave 5 admission-remediation execution order (2026-08-26)

This is a serial authority chain. No agent may implement a successor against a
mock, fixture, cache, URI, or structural substitute for its predecessor.

1. **P2 publisher repair owner.** Starting from P1 only, repair the
   `AuthorityPublicationJournalV1` first-use directory race (`EEXIST`): fsync
   every created ancestor, use a durable owner receipt, and compare/revalidate
   the exact observed stale owner/lock before unlink. Prove canonical-envelope
   replay/altered-input denial, real competing processes, and SIGKILL recovery.
   Public journals, `instanceof`, in-memory locks, path-blind recovery, and
   process-free tests are prohibited. P2 remains `NON-ADMITTED` until an
   independent highest-capability review PASS.
2. **Read-authority owner (blocked on P2).** Freeze only
   `SnapshotAuthorityPortV1`, opaque authority view, canonical target, and
   closed expected-read binding. `openBoundSnapshot` uses production registry/
   snapshot state through branded `TargetInventoryStoreV1.openPublishedAuthorityInventoryV1`,
   and rejects every swapped dual snapshot, manifest, instance,
   worktree, revision, target, and brand before authorization/projection.
   No raw manifest/map/cache, public journal, or duck-typed view is admissible.
3. **URI/projection owner (blocked on read authority).** Resolve URI and legacy
   alias to a candidate, prove sealed membership, verify the real branded
   receipt, compare every frozen receipt/binding field, then call ProjectionPort.
   Run hostile URI/Unicode/path/receipt/visibility matrices and canonical
   positives; raw filesystem paths, alias-only success, local signing, and the
   rejected URI candidate are forbidden.
4. **Cursor/MCP/materializer owner (blocked on URI).** Consume only the admitted
   binding; prove zero pre-admission projection calls, sealed continuation
   domain/position/limit, bounded pages, cache partitioning, and read-only
   materialization. Mock projection or synthetic cursor tests cannot advance
   admission.

For each owner: focused production oracle once, exact-scope diff inspection,
then independent normal/highest-capability review. A FAIL does not transfer
authority or scope to the next owner; it reopens only its sealed boundary.
This additive sequence preserves the existing normative authority/cursor ABI,
raw snapshot APIs, and exact `spipe-markdown-token-v1@1` <=6,000-token gate.
Rejected cursor code is forensic evidence only; no owner may delete or weaken
those contracts.

### 10.24 Wave 5a commit-publisher prerequisite (2026-08-26)

**Status: W5A authority primitive is `NON-ADMITTED`.** Existing stores persist
metadata/graph snapshots but lack the KnowledgeCompiler transaction required to
materialize and publish complete artifact/section/directory/project/aggregate
authority inventories. Synthetic manifests/maps cannot satisfy W5A-18/19.

| Lane | Exclusive ownership | Required output | Gate |
|---|---|---|---|
| W5A-P commit publisher | `src/core/knowledge_compiler_commit_publisher.js`, materializer, composition-root wiring | exact base/publication input, immutable base snapshot, sealed inventories/manifests, closure permit | W5A-25..27 parity/all-and-only contributor proof |
| W5A-S authority ports | `src/workspace/registry_authority_v1.js`, `src/storage/snapshot_authority_v1.js`, `src/storage/target_inventory_store.js` | branded revisioned registry/snapshot/inventory construction and store wiring | real owner construction before W5A-P/E |
| W5A-J publication journal | `src/storage/authority_publication_journal.js` | `AuthorityPublicationRecordV1`, fsynced staged objects/records/parents, atomic durable current-pointer CAS, sole recovery owner | W5A-28..29 fault/restart/concurrent-read/replay proof |
| W5A-E independent oracle | focused production fixtures | real roots/pages/projections and substitution evidence | W5A-30 + highest-capability PASS |

Frozen names: `KnowledgeCompilerCommitPublisherV1`, `CommitInputV1`,
`TargetInventoryMaterializerV1`, `ProductionInventoryBuildV1`,
`AuthorityPublicationJournalV1`, `PublishedAuthorityCommitV1`. Commit order:
open exact expected base/publication -> normalize deltas -> base snapshot -> exact registry -> complete project
inventories -> all-and-only aggregate -> seal -> closure permit -> fsynced CAS
publish -> recovery-safe acknowledgement. URI/MCP/materializer stays read-only.

Merge owner: `/root`; final reviewer: independent highest-capability reviewer.
No authority/cursor/URI/projection admission before W5A-P/J/E passes.

### 10.25 Publisher non-admission repair sequence (2026-08-26)

**Status: `NON-ADMITTED`.** The first W5A-P candidate may not be repaired by
loosening an oracle. It failed five ownership/evidence gates: public
journal/`instanceof` permit admission, non-canonical replay identity, shallow
current/recovery validation, non-durable inventory/manifest ownership, and
non-production crash/parity proof.

| Step | Owner | Required deliverable | Admission evidence |
|---|---|---|---|
| P1 | W5A-P + W5A-S | closure-branded `TargetInventoryStoreV1` path and canonical replay envelope hash | strings, structural objects, serialized permits, public journals, and caller roots deny |
| P2 | W5A-J | journal-owned content-addressed inventory/manifest objects, full record fields, atomic state machine | staged objects/record/current pointer survive fsync/rename/CAS/restart and replay exactly |
| P3 | W5A-J + W5A-E | deep current/recovery verifier and stale-lock/process-crash recovery | readers see only old/new complete record, never null/staged/partial; corruption denies |
| P4 | W5A-P + W5A-E | real clean/incremental publisher parity and sealed directory continuations | W5A-26, W5A-28, W5A-31..35 PASS against production filesystem owners |

`AuthorityPublicationRecordV1` must contain exact workspace/project/worktree/
revision IDs, expected registry/base/publication IDs, base and authority
snapshot IDs, ordered project roots, aggregate root, manifest digests, object
hashes, and canonical replay-envelope digest. The journal alone owns its
objects, transitions (`staging -> objects_durable -> record_durable ->
current_cas -> acknowledged`), recovery, and current pointer. W5A-P accepts no
parallel shortcut: cursor, URI, projection, MCP, and materialization remain
blocked until independent highest-capability review reports PASS.

### 11.2 Wave 5a sealed-publication repair gate (2026-08-26)

1. **Status/ownership.** The rejected pre-cursor authority candidate is
   forensic-only and `NON-ADMITTED`. W5A-A owns authority; W5A-C owns oracle
   fixtures; W5C/URI/MCP/materializer cannot edit until both independently PASS.
2. **Foundation.** W5A-A binds loaded manifest/inventory bytes to the exact
   dual-snapshot/registry tuple, recomputes roots, and revalidates live registry
   plus snapshot revision after open. The commit root alone mints a
   non-forgeable publisher permit through the sole
   `publishAuthorityInventoryV1({permit,build})` ABI and selects all-and-only schema-complete
   aggregate contributors.
3. **Directory/policy.** W5A-A seals ordered unique children, bounds, and a
   continuation domain derived only after manifest/inventory verification; no
   manifest root or digest commits it. W5C-A uses cross-process monotonic CAS
   and atomic rename with file/parent fsync, validates every schema, and
   recovers only a contiguous valid log.
4. **Evidence.** W5A-C/W5C-A must pass W5A-21..24 and W5C-13..14: substitution,
   revision windows, permits/aggregate completeness, page adversaries,
   cross-process races, and fault/restart recovery. Mock maps or in-memory
   tests are not evidence.
5. **Merge/review.** Merge owner `/root`; independent normal/highest-capability
   reviewer. Commit only after focused tests and PASS; do not push from this lane.

### 12.1 Wave 5a/5c production-authority correction (2026-08-26)

**Both prior sealed-read implementation attempts are non-admitted.** Do not
reuse their mocked source/evidence. Freeze branded production
`WorkspaceRegistryV1.resolveExactWorkspaceWorktreeV1`,
`SnapshotStoreV1.openExactSnapshotV1`, and
`TargetInventoryStoreV1.publishAuthorityInventoryV1/openPublishedAuthorityInventoryV1`.
Worktree UID grammar is `W-<opaque-base32>` only; `WT-*` denies. The authority
revalidates exact registry and snapshot revisions after published-manifest open.

| Lane | Additional owned deliverable | Admission evidence |
|---|---|---|
| W5A-A | non-forgeable production commit publisher and complete aggregate roots | atomic visibility; clean/incremental artifact/section/directory/aggregate parity; strings/structural permits deny |
| W5A-B | bounded directory page `1..100`, <=100 entries, <=200 lines, <=6,000 `spipe-markdown-token-v1@1` tokens | sealed child identity/order/page bounds and authenticated continuation |
| W5C-A | fsynced policy directory; monotonic CAS single-policy append-only policy/key/issuer/rotation/revocation family | restart plus create/write/fsync/rename/CAS faults |
| W5A-C/W5C-D | independent real-port oracle | W5A-16…20 and W5C-11…12 PASS |

Only KnowledgeCompiler's production commit path publishes inventory. Durable
operations use immutable UIDs: exact replay is idempotent; altered/stale input
fails closed. URI/MCP/materializer stays blocked until all listed gates pass.

## 12. Cursor authorization prerequisite (2026-08-26)

**Status: design frozen; implementation non-admitted.** The existing concrete
`AuthorizationPortV1` is Trust/Edge-only. Wave 5 URI/MCP/materializer work must
wait for the required §3.1 extension of that same branded port; no lane may
create a parallel signer or alter Trust/Edge receipt semantics.

| Lane | Exclusive ownership | Published boundary | Gate |
|---|---|---|---|
| W5C-A authorization | `src/core/authorization.js` owner | read/cursor grants, durable cursor key policy | exact domain/brand/binding/expiry/revocation evidence |
| W5C-B authority/projection | SnapshotAuthority + `src/view` integration owner | trusted expected read binding and sole ProjectionPort ABI | no raw authority claim or Projection call before proof |
| W5C-C URI/MCP | view/MCP owner | inbound/outbound cursor adapter | blocked on W5C-A/B PASS |
| W5C-D evidence | independent reviewer | real-port restart/rotation/fault matrix | W5C-01…W5C-10 PASS |

**Required ordering:** W5A-A/B/C first delivers and independently admits the
sealed production authority, ProjectionPort ABI, and W5A-01…20 evidence. Only
then does W5C-A extend AuthorizationPort against W5A's branded bindings and
pass W5C-01…12. W5C-B is an authority/projection-to-authorization integration
check, not a second authority/projection implementation, and cannot overlap
W5A-A/B ownership. W5C-C URI/MCP starts only after W5A and W5C-A/B PASS.

The only projection operations are
`render(authorityView,canonicalTarget,verifiedReadGrant)` and
`list(authorityView,directoryTarget,verifiedReadGrant,verifiedCursorGrantOrNull)`.
The inbound cursor is verified against the same opaque read grant before list;
the returned deterministic next position is sent to `issueCursorReceiptV1`
only after list. `VerifiedReadGrantV1` carries a sealed `ExpectedReadBindingV1`'s
trusted worktree UID, authority-instance UID, and authority-manifest digest,
despite its legacy read receipt not serializing the worktree field. The
canonical schemas and the only durable key-policy state machine are
architecture §21; no `lastSortKey`, `pageRequest`, or adapter-created grant is
an ABI.

W5C-A owns one durable `CursorReceiptKeyPolicyV1`, including unique rotation
records and `pending -> current -> grace -> revoked` transitions. It must make
the durable revocation-epoch advance restart-idempotent, preserve old
verification only during grace, and fail closed for a missing current private
KeyProvider handle. The final reviewer rejects any configuration that has a
second rotation record shape, non-durable transition, or a cursor binding
derived after read-grant verification.

## 11. Wave 5a snapshot-authority prerequisite and ownership (2026-08-26)

The current URI lane is **non-admitted**. `ImmutableSnapshotStore` lacks a
target inventory and workspace/worktree-bound authority view, so a direct URI
resolver cannot prove that a receipt's target kind/UID belongs to its pinned
snapshot. Do not start/reuse a URI implementation candidate until this port
slice is accepted.

| Lane | Exclusive ownership | Published boundary | Gate before downstream work |
|---|---|---|---|
| W5A-A Snapshot authority | `src/core`, `src/storage`, `src/workspace` integration owner | branded `SnapshotAuthorityPortV1`, opaque `SnapshotAuthorityViewV1`, inventory manifest | workspace/project/worktree/base-snapshot/authority-snapshot/revision and digest checks plus target membership |
| W5A-B Projection | `src/view` | branded `ProjectionPortV1` consuming authority views, proven targets, and opaque verified grants | no raw store, path inference, scan, refresh, or adapter-created grant |
| W5A-C Evidence | focused unit/integration fixtures and system-plan mapping | W5A-01 through W5A-15 oracle evidence | independent highest-capability PASS |
| W5-D URI/MCP/materializer | `src/view`, `mcp` | resolver/resources/tools adapters | waits for all W5A gates; a sealed alias yields only a candidate, authority proves its canonical target, then receipt authorization occurs |

The integration owner freezes these exact methods before sidecars work:
`openBoundSnapshot(binding)`, `resolveCanonicalTarget(view, target)`,
`resolveCanonicalAlias(view, alias)`, `listDirectoryTarget(view, selector)`,
`createExpectedReadBindingV1(view, canonicalTargetOrDirectory, normalizedRequest)`,
`ProjectionPortV1.render(authorityView,canonicalTarget,verifiedReadGrant)`, and
`ProjectionPortV1.list(authorityView,directoryTarget,verifiedReadGrant,verifiedCursorGrantOrNull)`.
The authority binding is exactly `{workspaceUid,
projectUidOrNull, worktreeUid, baseSnapshotUid, authoritySnapshotUid,
revisionId, registryRevisionId}`. `baseSnapshotUid` opens the exact immutable SnapshotStore tuple;
`authoritySnapshotUid` selects the matching content-addressed authority
manifest/inventory; the exact inventory-open binding carries both and neither
identity may be inferred from the other. The final reviewer
must reject structural substitutes, project-only snapshot reads, missing
manifest target inventory, and any URI rendering before target proof. This is
a read-only prerequisite and does not authorize an HTTP or write feature.

W5A-A additionally owns sealed `TargetInventoryManifestV1` roots. It must
define project versus `workspace_aggregate` scope. The aggregate's required,
canonical `contributingProjectRoots` field is the full ordered manifest of
`{projectUid, baseSnapshotUid, authoritySnapshotUid, targetInventoryRoot}`;
it is committed by both inventory and authority manifests, forbidden for a
project scope, and permits an explicit empty aggregate only. Resolver adapters
first open and verify the receipt-named snapshot only as an untrusted
candidate; a legacy alias yields only a canonical candidate, which must pass
sealed `resolveCanonicalTarget` membership proof; only then verify the receipt
against an `ExpectedReadBindingV1` created from that proof, including its
`authorityInstanceUid` and `authorityManifestDigest`. `worktreeUid` stays out
of the legacy serialized read receipt but is a trusted `VerifiedReadGrantV1`
claim, together with the two authority claims, copied from the sealed authority
binding and a signed cursor field. Evidence
must include tampered root, project mismatch, aggregate positives, and
cross-instance genuine-brand mixing before W5-D begins.

### 10.23 Wave 5 URI-foundation non-admission and fresh lane (2026-08-26)

1. **Attempt closed.** The Wave 5 URI-foundation candidate exhausted three
   independent review/fix cycles. It is uncommitted and not admitted; do not
   reuse its code. Wave 5 URI execution remains pending.
2. **Canonical alias gate.** The fresh owner resolves every legacy alias,
   including `spipe://skill`, only to a canonical candidate and proves its
   sealed target membership before issuing or accepting a receipt using the one
   exact v2 ABI frozen below. Verify the signed `D-` receipt through `AuthorizationPort`
   (supported version/key, canonical `spipe-uri-read-v1\0` payload, allow
   decision, live window, revocation epoch) before every call compares all
   fields against its direct proven target or reauthorizes/fails closed.
   Freeze exactly `CanonicalReadReceiptV1{receiptVersion, authorityKeyId,
   authorityKeyEpoch, normalizedAliasUriOrNull, canonicalUri, workspaceUid,
   projectUidOrNull, targetKind, targetUid, baseSnapshotUid,
   authoritySnapshotUid, revisionId, viewKind,
   normalizedLogicalPath, selectorDigest, effectiveScopeDigest, orderingVersion,
   pageLimitOrNull, policyVersion, decision, issuedAtMs, expiresAtMs, receiptUid,
   issuerKeyId, revocationEpoch, signature}` and `CursorReceiptV1` with the
   closed Wave 5a architecture schema: canonical alias/URI/target binding,
   worktree, algorithm, bounded `pagePosition`, and separate identity/signing
   preimages; `lastSortKey` is not an ABI field.
3. **Snapshot gate.** Directly validate immutable snapshot existence,
   workspace/project ownership, revision, and target membership; URI/query text
   is never authority.
4. **Evidence gate.** Table-drive workspace-root/view, artifact, section,
   trace, diagnostics, and legacy-alias URI families (search is a tool input)
   through malformed/overlong or unsupported URI; fragment/empty identity,
   query, percent/decode, traversal/slash/backslash/encoded separator/dot,
   drive/UNC/Windows-device/reparse/ADS/trailing-dot-space,
   Unicode-control/NFC-NFD-collision/mixed-case, cursor, forged/expired/
   signature-invalid/revoked or mismatched receipt, and hidden/absent matrices. Require
   bounded redacted failure evidence and independent highest-capability review
   before commit.
5. **Positive gate.** Assert canonical list/read/render success for workspace
   root/view, artifact, section, trace, diagnostics, legacy alias after
   canonical reauthorization, and `spipe_search`; alias success must return the
   authorized canonical target, not an alias-only echo.
6. **Fresh-v2 correction.** Before the new implementation starts, extend the
   frozen receipt tuple to include authority key/epoch, view, normalized
   selector/filter digest, ordering version, and page limit. Cursor receipts
   use only architecture §21.1's complete schema, including `receiptKind`,
   trusted signed worktree, algorithm, and bounded page position; they cannot
   be replayed against any selector, including a foreign workspace. The
   composition root must reject
   structural/duck-typed “verifiers”; only an opaque branded real signed
   `AuthorizationPortV1` creates verified grants. The workspace-root success
   case is exactly `spipe://workspace/{workspace}/`; its un-slashed form is a
   hostile malformed case. Record one public `not_found_or_unauthorized`
   response class for all read-admission denials, with private reason codes
   only in telemetry. These are acceptance blockers, not optional hardening.

Merge owner remains `/root`; final acceptance remains owned by an independent
normal/highest-capability reviewer.

### 10.22 Wave 5 virtual-view implementation-readiness lane (2026-08-26)

**Scope and non-overlap.** This lane owns read-only virtual MCP resources,
equivalent model tools, and optional safe materialization. It must not modify
the capped cursor/provider ABI or claim Wave 4/provider admission. It begins
from the normative `spipe_knowledge_compiler_mcp_views.md` contract and appends
only compatible evidence to the five knowledge-compiler companion documents.

1. **Primary owner — core/read adapters.** Define `WorkspaceRegistry`,
   `ResourceResolver`, `ProjectionPort`, snapshot-carrying resource/tool
   envelopes, and legacy transcript fixtures. Freeze URI, pagination, error,
   authorization, and cache interfaces before parallel work.
2. **Sidecar A — projection safety (N/A until interfaces freeze).** Independently
   review URI normalization, virtual-path collisions, UID/projection-UID
   distinction, deterministic ordering, visibility/cache partitioning, and
   bounded request behavior. It may add only tests after the frozen names land.
3. **Sidecar B — materializer safety (N/A until port interfaces freeze).** Build
   `MaterializerSafeFilesystemPort` provider evidence and race/fault fixtures;
   it may not add a raw Node mutation fallback or touch refactor ownership.
4. **Integration owner.** Assemble in the fixed order: resolver/projection;
   legacy stdio resources/tools; materializer; optional HTTP 2026 only after its
   separate authorization/invalidation evidence. Rebase exact-scope changes
   onto current main and preserve six legacy tools plus `spipe://skill`.
5. **Evidence and review.** Run each focused fixture once, inspect generated
   MCP manual quality, and obtain independent normal/highest-capability review
   of authority, cache, cursor, and filesystem claims. Required acceptance is
   the explicit Wave 5 evidence set in detail design §18; failures fail closed,
   with no widened scope.

Merge owner remains `/root`; final reviewer is an independent
normal/highest-capability agent. Notifications, subscriptions, editor VFS,
FUSE/ProjFS, and provider-backed semantics are explicitly `N/A` for first-slice
admission.

### 10.20 Fresh three-blocker ABI repair lane (2026-08-26)

**Scope:** exactly the five canonical knowledge-compiler documents; no product
code or tests. **Merge owner:** `/root`. **Final reviewer:** an independent
highest-capability reviewer after a separate implementation-readiness review.

1. Freeze the executor result union so generic `{code}` excludes
   `unauthorized`; require the sole unauthorized arm to carry a private exact
   seven-enum tombstone reason, persist it in the bridge, and redact it from
   every public result.
2. Freeze the sole page/replay order: request structural/type/cap checks;
   reservation; cursor identity/decode/verify/binding/liveness; replay or fresh
   work. The bridge alone tombstones every post-reservation cursor failure using
   the existing ordered reason table; no executor/store double ownership.
3. State the exact required `requestedLimit`/`requested_limit` range as positive
   safe integer `1..1000` in all session, request, wire, executor, result,
   evidence, and cap maps. Require oracle cases for 0/1/1000/1001/noninteger
   and reserve-before-cursor call traces.

**Exit gate:** static scope/contradiction checks plus both reviews PASS. This is
not product readiness: provider implementation/admission, Wave 4, AC-4, and
the integrated pipeline stay open.

### 10.17 Cursor-authority mapping and provider handoff (2026-08-26)

1. **Representation decision — frozen.** After reservation, an unclassified
   trusted cursor-authority `identity`, `sign`, or `verify` malfunction first
   stores legal tombstone reason `interrupted`, then returns public
   `internal_error`. Do not add `internal_error` to the tombstone enum.
   Specific already-established expiry, revocation, binding,
   authority-generation, policy, or record-corruption classifications retain
   precedence.
2. **Next implementation session.** Implement the frozen mapping and oracle
   cases without broadening either closed vocabulary. Prove tombstone-before-
   return ordering, identical-retry fail-closed behavior, and the precedence
   cases.
3. **Downstream lanes — waiting.** Provider admission, Wave 4, AC-4, and the
   integrated pipeline remain open.

Merge owner remains `/root`; independent normal/highest-capability review is
still required for the next frozen contract and implementation.

### 10.18 Full ABI consolidation stop and next owner (2026-08-26)

1. **Consolidation attempt — `FAIL`.** The eleven-item ABI consolidation
   exhausted the mandatory three review/fix cycles. It made no product edit,
   ran no product test, admitted no contract, and pushed nothing. Retain
   `e5c556de59d` at `/tmp/spkc-provider-abi-full-uWb9kD/repo` as immutable
   forensic evidence only; do not copy its rejected contract text.
2. **Review split.** Implementation-readiness review passed. Independent
   highest-capability review failed because Section 17.11 excludes Section
   17.7.1 but depends on its exact `providerSession`, authority, and executor
   schemas, and excludes Section 17.7.9 without restating the complete public
   error record/field shapes and exhaustive precedence.
3. **Fresh-session task.** Restate both definition families completely inside
   Section 17.11. Do not inherit excluded control prose or claim readiness
   until a new independent highest-capability review passes.
4. **Downstream lanes — waiting.** Provider readiness and admission, Wave 4,
   AC-4, and the integrated pipeline remain open.

Merge owner remains `/root`; final acceptance remains owned by an independent
normal/highest-capability reviewer.

### 10.19 Self-containment repair stop and next owner (2026-08-26)

1. **Repair attempt — `FAIL`.** The self-containment repair exhausted the
   mandatory three review/fix cycles. It made no authoritative contract or
   product edit, ran no product test, and pushed nothing. Retain
   `e77cb713d5703d864f32d16ab3abab0afb5d3215` at
   `/tmp/spkc-provider-self-contained-JdUR6t/repo` as immutable forensic
   evidence only; do not copy its rejected clauses.
2. **Review split.** Implementation-readiness review passed. Independent
   highest-capability review failed on three exact blockers: the generic
   code-only unauthorized arm overlaps the provenance arm; pre-reserve
   binding/cursor prose conflicts with traces reserving before
   `Cidentity`/`Cverify`; and `requestedLimit` lacks its exact range despite the
   candidate cap.
3. **Fresh-session task.** Make the executor-error union structurally disjoint,
   freeze one reserve/cursor order and tombstone owner, and specify
   `requestedLimit` as `1..1000`. Require fresh static checks and independent
   highest-capability admission before implementation.
4. **Downstream lanes — waiting.** Provider readiness/implementation/admission,
   Wave 4, AC-4, and the integrated pipeline remain open.

Merge owner remains `/root`; final acceptance remains owned by an independent
normal/highest-capability reviewer.

### 10.21 Provider implementation non-admission and fresh-design gate (2026-08-26)

1. **Attempt closed before runtime.** The provider implementation candidate at
   `/tmp/spkc-provider-admission4-kVaqO2/repo`, based on
   `f7ec2dc1b0c0de4b42bb97940b17bec9db29e5a1`, stopped after two immutable xhigh
   pre-runtime `FAIL` reviews. The final review attempt added no edit to its
   exact ten-file scope and ran no runtime test, commit, or push. The forensic
   candidate itself has an existing dirty diff; treat its code and contract
   prose as forensic material only.
2. **Decisive blocker.** Section 17.14.3 assigns post-reservation cursor
   identity/decode/verify to the bridge, but the frozen seven-field bridge
   factory configuration has no cursor-authority port. This is a configuration
   ABI contradiction, not an implementation choice.
3. **Non-admitted behavior.** Mandatory tombstones, the exact executor-error
   union, full replay verification, cursor digest, store
   accounting/idempotency, closed-object accessors, and oracle vectors remain
   unimplemented and are not evidence.
4. **Fresh-session task.** A new design owner must resolve the factory/config
   ABI before assigning any implementation work. Then require fresh
   implementation-readiness and independent highest-capability review.
5. **Downstream lanes — waiting.** Provider admission, Wave 4, AC-4, and the
   integrated pipeline remain open.

Merge owner remains `/root`; final acceptance remains owned by an independent
normal/highest-capability reviewer.
