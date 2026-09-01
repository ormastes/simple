<!-- codex-research -->
# SPipe Knowledge Compiler — Non-Functional Requirements

**Status:** Selected / final  
**Date:** 2026-08-25  
**Source:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`  
**State acceptance criteria:** `.spipe/spipe_knowledge_compiler/state.md`

## Requirements

### Correctness and determinism

#### NFR-SPKC-001 — Deterministic output

Given identical canonical content, configuration, provider versions, and revision state, clean builds and repeated runs must produce byte-stable schemas/serialization where specified, stable graph identities, deterministic ordering, deterministic projections, and no rebalance churn.

Evidence: golden snapshots and repeat-run comparison. Traces: AC-3, AC-4, AC-5, AC-9.

#### NFR-SPKC-002 — Incremental parity

Any supported sequence of incremental additions, updates, deletes, renames, and worktree-overlay changes must converge to the same graph, diagnostics, lexical ordering, and views as a clean rebuild of the resulting canonical state.

Evidence: property/metamorphic fixtures. Traces: AC-3, AC-4, AC-8.

#### NFR-SPKC-003 — Portable degradation

Core indexing, exact lookup, lexical search, graph traversal, trace checks, views, and refactor safety must remain usable without Simple, embeddings, remote services, editor integration, or OS virtual mounts. Optional-provider failure must degrade explicitly to supported local behavior, never to a false PASS.

Evidence: standalone SPipe and provider-failure scenarios. Traces: AC-4, AC-12, AC-14, AC-15.

#### NFR-SPKC-004 — Read-only and fail-closed defaults

Virtual views and ordinary discovery operations must be read-only. Every mutation must require the relevant capability and approval policy; missing, invalid, stale, or ambiguous authority must fail closed.

Evidence: negative authorization and virtual-write tests. Traces: AC-5, AC-7, AC-14.

### Security, privacy, and isolation

#### NFR-SPKC-005 — URI and path containment

All URI/path inputs must use one documented cross-platform grammar with canonical percent-decoding, Unicode normalization, separator, drive-letter, UNC/device-name, case-folding, reserved-name, and trailing-dot/space rules. Inputs must reject traversal, double/ambiguous encoding, absolute-path injection, alternate-data streams, and cross-root escape. Authorization decisions must use explicit project/revision namespaces and descriptor-relative traversal beneath pre-opened trusted roots; materialization/refactoring must use no-follow/open-beneath equivalents plus post-open identity checks so a symlink, junction, mount, or rename race cannot replace a validated ancestor or target.

Evidence: traversal and symlink/junction escape fixtures. Traces: AC-14.

#### NFR-SPKC-006 — Visibility and authorization isolation

Search, resources, generated views, caches, logs, diagnostics, explanations, counts, timing, and server adapters must preserve artifact visibility and trust without existence side channels. Private or authorization-sensitive results must never enter public/shared cache scope; cache keys and validators must include authenticated principal or authorization-equivalence class, visibility, policy version, workspace/revision, and query scope. Database-server access must preserve existing deny-wins collection/field capability behavior. Retrieved artifact text and provider output must remain delimited untrusted data and must not alter system/tool policy, authorization, approval, or prompt instructions.

Evidence: tenant, field, cache-scope, and prompt-trust tests. Traces: AC-6, AC-12, AC-14.

#### NFR-SPKC-007 — Embedding privacy and safe failure

Local semantic providers must be the default. Remote semantic processing requires explicit project policy; excluded/private paths must not be transmitted. Cache identity must include model, model revision, preprocessing version, content hash, and visibility. Failure must retain exact/BM25/graph behavior.

Evidence: policy and injected-provider-failure tests. Traces: AC-4, AC-10, AC-14.

#### NFR-SPKC-008 — Transaction integrity

Refactor operations must authenticate and authorize plan and apply separately; apply must consume a short-lived single-use operation token cryptographically or equivalently bound to principal, worktree, snapshot, operation digest, exact targets, and expiry. They must use hash/revision/file-identity preconditions, descriptor-relative no-follow operations, journal-before-write with original content and security-relevant metadata, atomic replace/move where supported, directory sync where required, startup recovery, and exact rollback. Rollback must preserve or explicitly diagnose permissions, ownership where controllable, executable bits, timestamps where required, aliases, graph state, and generated state. Critical profiles must define durable sync and immutable/signed evidence requirements.

Evidence: fault injection at each transaction phase and post-recovery hash/graph equality. Traces: AC-7, AC-14.

#### NFR-SPKC-009 — Worktree isolation

Committed immutable content-addressed segments may be shared only after content, schema/provider version, visibility, and authorization scope validation. Dirty overlays, locks, operation tokens, journals, generated views, provider processes, and mutable state must be isolated per worktree and principal where applicable. One worktree's uncommitted state, lock, recovery, cache, or authorization context must not affect another's query or mutation state.

Evidence: simultaneous divergent-worktree integration test. Traces: AC-3, AC-7, AC-8, AC-14.

#### NFR-SPKC-010 — Linked-project resolution safety

Cross-project identity must include project UID, revision, configured trust, and authorization scope. Registry/mount resolution must use the canonical URI/path grammar and descriptor-relative containment rules. Missing, mismatched, relocated, untrusted, or unauthorized linked projects must produce non-leaking diagnostics and must never resolve to a similarly named local artifact or inherit the caller project's trust.

Evidence: missing/uninitialized/mismatched linked-project fixtures. Traces: AC-3, AC-8, AC-14.

### Bounded behavior and search equivalence

#### NFR-SPKC-011 — Bounded model context

Generated directory reads must paginate above 100 direct entries and must normally remain at or below 200 Markdown lines and approximately 6,000 model tokens. Configuration must set enforceable maximum input bytes, decoded bytes, nesting/heading depth, tokens, terms, Boolean/phrase clauses, wildcard/fuzzy expansion, graph nodes/edges/depth, candidates, result bytes, provider response bytes, wall time, CPU work, and memory per parser/query class. Search, trace, diagnostics, and materialization must expose bounded limits/cursors; cursors must be opaque, integrity-protected, expiring, and bound to principal, scope, query, and immutable snapshot. Provider semantic deadlines must be checked over the inclusive 1..30,000 millisecond range from the first accepted frame-header byte, including ingress and response construction. A pre-binding transport failure must emit no wire response; its local diagnostic must contain no request payload or untrusted reflected binding. Budget exhaustion must return a stable partial/error status and must not silently broaden or claim completeness.

Evidence: oversized-directory and result-set fixtures. Traces: AC-5, AC-14.

#### NFR-SPKC-012 — Provider ordering parity

For the shared golden corpus and query configuration, the JavaScript fallback, Simple common scorer, DBFS adapter, textual DB adapter, embedded DB adapter, and server DB adapter must return equivalent deterministic ordering and stable document-ID tie breaks. Explanations must identify any intentionally provider-specific capability.

Evidence: cross-provider golden tests. Traces: AC-4, AC-12.

#### NFR-SPKC-013 — Exact optimized top-k

WAND, Block-Max WAND, segmentation, and shard merge optimizations must return exactly the same ordered top-k result as exhaustive scoring for the same snapshot, query, filters, and tie-breaking policy.

Evidence: exhaustive-versus-optimized property tests. Traces: AC-12.

### Performance and scale

#### NFR-SPKC-014 — Incremental efficiency

On the qualified Wave-0 corpus, machine profile, and benchmark command, the median warm elapsed wall-clock time for a single-document graph/index update must be at least 20 times lower than the median warm elapsed wall-clock time for a clean full rebuild of the same resulting state. The benchmark must use identical environment controls and enough repetitions to report distribution and variance; CPU time and peak RSS must be retained as diagnostics but do not replace the normative wall-clock ratio.

Evidence: reproducible benchmark report. Traces: AC-4, AC-14.

#### NFR-SPKC-015 — Evaluation latency and capacity

The implementation must be evaluated at 50,000 artifacts, 1,000,000 combined section/symbol/test nodes, 10 linked projects, and 5 concurrent worktrees. Provisional targets are warm lexical-query P95 below 100 ms and single-document incremental-update P95 below 100 ms on the documented development-workstation profile. Wave 0 must lock the machine, corpus, warmup, sample count, and final release budgets before these provisional values become release gates.

Evidence: versioned benchmark fixture and report. Traces: AC-12, AC-14.

#### NFR-SPKC-016 — Compatibility-path performance

No-op `spipe doctor` and existing compatible commands must not regress more than 10% on the locked Wave-0 benchmark. View materialization must rewrite only content-hash-changed generated files. Duplicate/promotion discovery must use sparse candidates rather than global all-pairs semantic comparison.

Evidence: before/after benchmark and file-rewrite audit. Traces: AC-10, AC-15.

### Stability, compatibility, and maintainability

#### NFR-SPKC-017 — Rebalancer stability and explainability

Rebalancing must preserve every hard constraint, produce connected communities, retain stable cluster identities, and be deterministic on unchanged input. Every proposed move and objective delta must be explainable. Hysteresis, cooldown, and minimum-improvement gates must prevent oscillation; final values are design/configuration decisions calibrated from accepted repository history.

Evidence: adversarial fixtures and repeated-snapshot stability tests. Traces: AC-9, AC-14.

#### NFR-SPKC-018 — Promotion fidelity

Promotion must preserve provenance, conflicting clauses, visibility, and project-specific constraints. A promoted unit and its `extends`/overrides must pass every consuming project's applicable verification before duplicate local knowledge is removed.

Evidence: multi-project promotion and conflict fixtures. Traces: AC-10, AC-14, AC-16.

#### NFR-SPKC-019 — Cross-platform/client compatibility

Supported behavior must be verified for standalone and linked repositories, Git worktrees, Unix symlinks/mount races, Windows junction/reparse-point and drive/UNC/device/path semantics, case-sensitive and case-insensitive filesystems, file-only agents, authenticated HTTP clients, negotiated legacy/current MCP clients, and any editor adapter that is declared supported. Unsupported atomicity or descriptor-relative primitives must be detected and fail closed or use a separately verified safe platform adapter.

Evidence: platform/client compatibility matrix. Traces: AC-5, AC-6, AC-14, AC-15.

#### NFR-SPKC-020 — Executable evidence quality

Public behavior must be covered by executable SSpec scenarios with real assertions and built-in matchers, plus mirrored Markdown manuals usable without opening test source. Unit/integration coverage must meet the repository's implementation policy, including at least 80% branch coverage where applicable. Empty bodies, placeholder passes, inferred-only strict evidence, and silent optional-provider skips are forbidden.

Evidence: SPipe stub scan, coverage report, executable specs, and reviewed manuals. Traces: AC-13, AC-15, AC-17.

#### NFR-SPKC-021 — Reproducible verification evidence

Security, privacy, path containment, authorization, transaction recovery, retrieval parity, trace completeness, performance, and scale claims must each name a reproducible command/fixture and retain authoritative output or generated report. A missing or unavailable optional provider is not passing evidence for that provider.

Evidence: verification matrix and reports. Traces: AC-13, AC-14, AC-17.

#### NFR-SPKC-022 — Dependency and boundary discipline

The baseline Node implementation must add no runtime dependency. Transport, authentication/authorization, storage, parser, graph, search, provider supervision, projection, diagnostics, refactor, rebalance, promotion, and skill-generation responsibilities must remain behind explicit least-authority interfaces. Only the refactor service may mutate canonical files; only promotion may publish approved common knowledge; only the skill compiler may emit executable policy surfaces. Providers and parsers must receive the minimum filesystem/environment/network authority required and must not inherit ambient credentials by default.

Evidence: dependency audit and module-boundary review. Traces: AC-2, AC-15, AC-17.

#### NFR-SPKC-023 — Canonical path stability

Public/protected canonical paths and lifecycle roots must carry a high migration penalty and must not move without explicit approval. Similarity-based raw-move recovery must be bounded and must not invoke unbounded quadratic comparison on large candidate sets.

Evidence: protected-path and bounded-candidate tests. Traces: AC-7, AC-9, AC-14.

#### NFR-SPKC-024 — Generated-surface freshness

Generated skill, rule, manual, projection, and compatibility surfaces must identify their canonical source and generator where applicable. Trust-bearing generated surfaces must use only the closed `trust_scope` values `untrusted_data`, `reviewed_reference`, or `executable_policy`; unknown or absent values default to `untrusted_data`. Trust scope must derive from an authorized canonical registry record, never from content or a provider response, and every elevation to `reviewed_reference` or `executable_policy` must record authorized principal, capability, source UID/hash/revision, policy version, decision time, and audit evidence. Verification must re-authorize the current registry record and source digest, detect revoked/downgraded authority, and reject stale, manually diverged, misplaced, duplicate, unauthorized, or trust-escalated generated artifacts.

Evidence: generation idempotence and stale-surface tests. Traces: AC-11, AC-13, AC-16.

#### NFR-SPKC-025 — Convergent verification and delivery

Final verification must trace every acceptance criterion to authoritative current-state evidence, include independent highest-capability review of sidecar findings and generated-manual quality, use no more than three distinct verify/fix cycles, and never rerun an unchanged green check. Verified increments must be isolated from unrelated concurrent work and follow the repository's linear sync/push safety process.

Evidence: final verification matrix, review record, command log, and commit/file-count evidence. Traces: AC-17, DC-1.

### Selected host-authority profile

#### NFR-SPKC-026 — Authority-service safety, availability, and performance

The transactional authority service is a required P3 availability dependency for publication and canonical authority open. It must use mutually authenticated service/client identity, least-authority operation capabilities, workspace/tenant isolation, replay protection, durable audit records, and fail-closed authorization. Its own durable decision, never a client cache or filesystem pointer, is authoritative.

An invalid authenticated capability, authorization binding, scope, or trust epoch before journal admission must return explicit non-enumerating `CapabilityDeniedV1` with no mutation or receipt; authentication/availability/transport failure instead returns the separate `ServiceTransportFailureV1` request-layer failure. Both are outside the closed P3 outcome algebra. A timeout, partition, or lost response may occur after the service has made a durable authority decision. In that case the client must never infer success, publish locally, or fall back: it must resolve the immutable request/idempotency key and receive the exact accepted terminal/winner evidence or a definitive no-admission result. The service must publish explicit RTO/RPO, backpressure, queue, single-writer or quorum, fencing, and split-brain prevention policies; acknowledgement before durable decision is forbidden. Wave 0 must set measured local and remote P95/P99 publish/open latency, durable throughput, queue bounds, and restart-recovery targets. Measurements must include contention, crash/replay, lost-response resolution, and service-unavailable cases, and no target may trade away durability or linearizability.

Evidence: deterministic pre-admission capability-denial and authentication/unavailability fixtures proving `CapabilityDeniedV1` and `ServiceTransportFailureV1` have no journal admission, receipt, or mutation; deterministic commit-then-lost-response and partition/replay fixtures proving idempotency-key resolution returns the exact accepted terminal/winner or definitive no-admission; plus independent multi-client, SIGKILL/restart, authorization, load, and latency fixtures proving exactly one linearizable winner and no client-side publication fallback. Traces: AC-5, AC-7, AC-8, AC-14, AC-17.

#### NFR-SPKC-027 — Optional native-provider certification

An optional native authority backend must be capability-bound, input-validated, memory-safe, and fail closed on every unadmitted host/filesystem tuple. For each admitted OS/kernel/filesystem/version tuple, certification must prove exact raw-byte predecessor behavior (including paired-null genesis), exclusive fencing, parent durability, SIGKILL recovery, the closed errno/result map, and golden ABI parity with the authority service. The compatibility matrix must prove every other tuple, including Node, is unavailable before P3 stages or mutates publication state. Recertification is required whenever the native runtime, kernel, filesystem, or provider changes.

Evidence: per-tuple stress/fault/errno fixtures, contention/recovery measurements for fsync, fencing, and conditional replacement latency, and a negative activation matrix. Traces: AC-7, AC-14, AC-17.

## Acceptance-Criteria Trace Summary

| State AC | Primary NFRs |
|---|---|
| AC-1 | NFR-SPKC-001–027 (selected NFR set) |
| AC-2 | 009–010, 017–019, 022–024 |
| AC-3 | 001–003, 009–010 |
| AC-4 | 001–003, 007, 012–016 |
| AC-5 | 001, 004–006, 011, 019, 026 |
| AC-6 | 005–006, 011, 019, 022 |
| AC-7 | 004, 008–010, 023, 026–027 |
| AC-8 | 002, 008–010, 020–021, 026 |
| AC-9 | 001, 017, 023 |
| AC-10 | 003, 007, 016, 018 |
| AC-11 | 024 |
| AC-12 | 002–003, 006–007, 012–016 |
| AC-13 | 020–021, 024 |
| AC-14 | 003–021, 023, 026–027 |
| AC-15 | 003, 016, 019–022 |
| AC-16 | 018, 020–021, 024 |
| AC-17 | 020–027 |
| DC-1 | 025 (delivery control, separate from product AC-1–17) |

## Design-Owned Measurement Decisions

Architecture/detail design and Wave 0 must make these requirements falsifiable by fixing:

- benchmark workstation, operating-system, corpus, warmup, repetitions, and percentile method;
- warm wall-clock sampling/warmup controls plus CPU, memory, and index-size diagnostic collection tooling;
- critical transaction durability/fsync and signed-evidence profiles;
- supported-client/protocol/platform matrix and capability negotiation details;
- rebalancer stability thresholds and reference-history calibration set;
- exact generated-surface provenance format and stale-detection command.
