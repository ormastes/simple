# SCV integration detail design and shared contracts

Date: 2026-10-27. Status: proposed contracts and algorithms; no implementation changes or runtime tests in this planning lane.

## Existing formats and adapters

Retain `CompileSnapshotV1`, phase 2 frontend schema/parse-source digest rules, package action V1–V4, existing distributed UID/alias types, reducers/allocation planning, and SHA-256 v1 signed DB payloads. The [source inventory](../01_research/local/scv_full_phase2_2026-10-27.md) separates concrete owners from proposed APIs. Do not infer compatibility from similar type names.

Proposed `CompileSnapshotV1Adapter` wraps a legacy frozen view into the V2 logical facade. Its outcome is either a fully represented view with coverage evidence, a restricted view whose unsupported capabilities are explicit, or refusal. It never synthesizes empty editor/generated/external roots. The compiler-facing adapter binds actual parser source bytes/SHA, inventory generation, declared source roots, target/configuration and exact source-read handles. Legacy V1 consumers keep original semantics.

## Frozen-read and receipt algorithm

1. Resolve accepted policy and immutable overlays/configuration/path rules; drain acknowledged capture through the requested barrier.
2. If event coverage is unknown, reconcile exact affected scope or refuse a complete snapshot. Freeze all required inventories, roots and generation before opening compiler tasks.
3. Return immutable object handles and file/directory/query witnesses. A consumer cannot reopen the worktree as a fallback.
4. Lookup a candidate artifact by its original key semantics or proposed SemanticActionV2; retain its full original forward read manifest.
5. Verify every recorded file, membership, positive/negative resolution, semantic facet, target and configuration observation against the requested snapshot. Unknown mandatory facet/provider/version yields unknown/rebuild.
6. Reuse only verified artifact bytes plus a receipt binding requested snapshot, action/manifest digest, verifier/provider versions, coverage, relevant policy and authorization. Provenance is separate. Publish the receipt durably without changing semantic artifact bytes.
7. On miss, schedule through existing TaskRunner, publish compiler stages/manifests, and repeat admission for the frozen subject. Edits after the barrier cannot silently change that subject.

For zero-work hits, inspect output identity/materialization first. Valid existing destination needs no rewrite; missing destination materializes verified cache bytes without codegen/link. SRC→OBJ is default; BIN/LIB/SMF are explicit downstream actions. TestRunner needs separate runtime/test-data/environment witnesses even when build outputs reuse.

## Manifest publication and projections

`publish_consumer_generation` is a proposed single-owner atomic operation over `(snapshot, consumer, source_generation, producer_attempt)` and a complete replacement manifest. Validate source/dependency subject and generated TLDR/output roots; derive reverse projections and unique generic demand; publish one root/journal transaction. Retries with the same idempotency identity/payload return the same result; incompatible payload reuse rejects. Failed/stale/cancelled attempts leave prior admitted manifests intact.

Pointcut changes invalidate old plus new candidate universes including negative matches. Compiler recomputes semantic matches/interfaces; SCV updates exact directory/search-domain witnesses. Macro additions invalidate prior absence even without a reverse user edge. Generic arguments use structured tagged canonical keys. Cyclic imports condense into SCCs; ordering optimizes layout and never deletes dependencies.

An advice-only behavior update must not introduce public type/layout changes; interface-producing advice declares introduced surface in its contract/TLDR. Runtime acceptance checks emitted symbols/layout/behavior against cold compilation, not only decoded byte equality.

## Domain solver transaction

The host binds accepted domain/routing/schema/provider/profile versions, base/sides, verified operations, readable capabilities and shared logical/memory budgets. It preserves inputs before running parser/model/solver stages. Solvers return typed proposals/conflicts/needs-inputs/resource outcomes; validators independently check exact candidates; Publisher checks expected authority state and complete required evidence.

DB schema resolution precedes row interpretation; UID identity precedes rename alignment. Old-schema writes require explicit UID/type mapping. Absent, null, value, defaulted interpretation and tombstone remain distinct. Lazy constant defaults bind the introduction/migration revision. Volatile defaults and type conversions require explicit deterministic migration/backfill evidence. Constraints validate the combined accepted snapshot/read set, catching cross-row write skew.

Settlement extends current allocation planning: original UIDs, candidate aliases, reference projection, allocator state and accepted batch record share one root. Candidate sequences are not final promises. A CAS race replans; a lost acceptance reply reconciles batch ID plus payload digest through authoritative read-back. No alias recycling or timestamp identity/winner rule.

## Storage, execution and error contracts

Secure raw-byte identity, byte-node reconstruction identity, typed semantic identity, representation identity and stable entity UID are distinct. Complete syntax nodes/sibling runs and complete DB records supply logical boundaries. Codec blocks/transport pages do not become source identities. Oversized indivisible input streams intact; unsupported parse regions remain explicit opaque units.

Digest algorithms/purposes and canonical domain versions are tagged. Fast collisions require canonical byte/equality checks; secure consumers cannot downgrade. Compute only required/lazy secondary hashes. Shared BLAKE3 source supports broad paths by description; upstream vector execution is still required. Source restore must not require loading historical parsers/solvers.

Untrusted providers get bounded immutable reads and no ambient clock/random/network/filesystem/publication capabilities. Cancellation/resource/output-size/malformed-result failures never publish partial success. Native subprocess/WASM isolation requires executed sandbox evidence; declarations alone do not establish enforcement.

Objects, graph projections, receipts and outbox records publish through durable root/WAL ordering with explicit acknowledgements. Journal replay returns old or complete new state, not a half-admitted manifest. GC roots include unresolved conflict inputs, unpublished work, dictionary/delta bases, alias/tombstone/frontier interpretation, active reader leases and pins. Only rebuildable accelerators are normal eviction candidates.

## Shared SSpec design vocabulary

Proposed helpers are `setup_scv_fixture`, `freeze_scv_candidate`, `exercise_scv_operation`, `collect_scv_evidence`, `check_exact_subject`, `check_byte_preservation`, `check_expected_conflicts` and `check_cold_warm_equivalence`. Manual-facing steps are `setup`, `capture`, `exercise`, `evidence`, `assert`. A later executable placeholder must fail explicitly with `fail("SCV scenario not implemented")` or `assert(false)`; no helper may imply pass through an empty body.

The [test plan](../03_plan/sys_test/scv_full_phase2_2026-10-27.md) specifies typed evidence and exact oracles. This deliverable does not install placeholder executable specs or manufacture generated execution manuals. Executable specification and native evidence are outstanding implementation-handoff gates.

## Numerical budgets and UI

There is no new UI workflow in this planning lane, so TUI/GUI mockups are N/A. Capture/merge/build APIs must expose durable versus pending, complete versus unknown, draft versus accepted, and blocked/conflicted reasons to future callers. No speculative numerical latency/RSS target is promoted to requirement. Measure startup, warm request, max RSS, barrier/reconciliation cost and retained growth before selecting deployment budgets.
