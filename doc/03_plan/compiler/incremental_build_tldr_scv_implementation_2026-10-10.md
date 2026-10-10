# Incremental compiler design: selected requirements and actual gaps

Authority: `simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md`, all 14 sections read, SHA256 `128a5f947662e9d10bc8267aa57bac455a243251af29df4187df4f6be47b2b3a`. Source review cut: release `f429fd4967b8051094067090f77399602f20e869`. The user requested this complete design; these are selected requirements, not an options questionnaire. The separate SIMD/GPU/Sosix document is missing and is not substituted or covered here.

Status: implementation incomplete; native verification and SPipe doc generation UNRUN. Earlier closed service/parser/SCV diagnostics do not establish this feature. Private JSON diagnostic receipts are bootstrap evidence, not the proposed production metadata format.

## Section coverage

| Design section | Requirements retained | Actual owners and gap |
|---|---|---|
| 1 Executive decision | REQ-001 one shared service, content identities, standalone fallback; REQ-016 binary-first qualification | Compiler cache and runner exist separately; no complete connecting vertical slice. |
| 2 Existing implementation | REQ-002 extend existing contracts and stores | PackageTldrHeaderV1, ActionRootJournalV1, SCV metadata/WAL, parser session and cache gateway exist. Names alone do not establish integration. |
| 3 Ownership/interfaces | REQ-003 pure common contracts and one mutation owner; REQ-004 immutable complete snapshots | No SourceEditV1/SourceChangeBatchV1/SourceChange validation APIs found in scoped release source/tests. Existing CompileSnapshotV1 already describes sources, resolution/negative witnesses, generated inputs, config/providers. Reuse these identities; do not invent competing compiler roots. |
| 4 Capture/recovery | REQ-005 adapters; REQ-006 reconcile; REQ-007 codecs; REQ-008 durability/migration | DocumentRegistry applies versioned edits; SCV records TSInputEdit and has coalescing. They do not emit the proposed shared batch. SCV metadata schema remains scv-metadb-1. Binary SMET and complete publication/outbox integration absent in inspected owners. |
| 5 Freshness | REQ-009 root domains; REQ-010 complete inventory; REQ-011 semantic invalidation; REQ-012 checkpoint delta | package_tldr_admit_v1 binds source and variant, early-cutoff compares semantic digests. Project expected-inventory verifier and exact all-domain receipts remain gaps. Private SCV source/header generation bridge and batching are partial, unqualified implementations. |
| 6 SCM checkpoint | REQ-013 revision association; REQ-014 writer serialization; REQ-015 hint-only index | Existing SCV metadata/revision and local CI receipt patterns are reuse points; no selected TldrFreshnessReceiptV1 API found. Git notes must verify target tree, scope/config and CAS availability; branch/time are not authority. |
| 7 DAG | REQ-016 binary-first states; REQ-017 mandatory join; REQ-018 safe conditional commit | BuildRunner reexports common task scheduler, journal has leases and append/history. No PostBuildTaskV1 or complete freshness coordinator found. Default source commit and remote push remain off. |
| 8 Cache/SMF/bootstrap | REQ-019 standalone gateway; REQ-020 shared parse ownership; REQ-021 artifact layout; REQ-022 selective bootstrap | Embedded gateway and package SMF validation exist. Actual warm typed header consumers need versioned producer/validator/consumer integration. Parse reuse needs retained generation lifetime across TLDR, compile and TestRunner. Bootstrap authority currently rejects oversized physical trees; safe captured projection is being implemented separately. |
| 9 Failure/security | REQ-023 fail closed and recover; REQ-024 bounded ownership | Crash, torn frame, missing CAS, changed source, failed metadata, remote trust and process closure require actual owner controls. No unconditional progress proof: dead-owner release needs parent-authoritative death/requeue. |
| 10 Work packages | WP0–WP11 below | All packages retained; no completion inferred from a private helper or index test. |
| 11 Acceptance/performance | REQ-025 parity and weighted evidence; REQ-026 observability | Unit, integration, benchmark and fault matrices below; actual counters with reason codes, no synthetic verified totals. |
| 12 Commands/defaults | REQ-027 commands and separate visible states | Proposed command spelling needs existing dispatcher integration, help and config admission. Standalone requires zero mandatory runner/SCV/Git process launches. |
| 13 First slice | REQ-028 complete conservative vertical slice | Shared adapter batch → existing SCV WAL → conservative verifier → exact receipt → status/history → remaining-work postcheck. Precise incremental parser/remote CAS comes after this. |
| 14 References/notes | REQ-002 compatibility and evidence provenance | Preserve existing wire formats and owner boundaries. Local current source is authoritative for implementation; historical references are design context. No external facts or fresh web claims are needed for this local gap audit. |

## Reused source owners

- `src/lib/editor/document/{transaction,registry,model}.spl`: ordered byte edits, inverse transaction, version and save state. Add an adapter/outbox; do not duplicate undo history.
- `src/lib/scv/{metadata_db,parser_session,sj_capsule,compile_snapshot,compile_source_inventory}.spl`: existing durable history, leases, captures and reconciliation. Metadata tables use the first column as key; add synthetic keys for multi-row entities and migrate additively.
- `src/compiler/00.common/cache_contract/{snapshot_contract_v1,semantic_read_set_v1}.spl`: logical path policy, byte blob, provider/config/negative resolution identities and effect replay policy. Extend exact witnesses, not a parallel algorithm.
- `src/compiler/80.driver/cache/{package_tldr_metadata,gateway/cache_gateway_adapter,journal/action_root_journal_v1}.spl`: summary admission, embedded gateway and action checkpoint. Existing package admission is per-header, not a complete project verification proof.
- `src/compiler/10.frontend/{frontend,frontend_parse_cache}.spl` plus flat-pool codec: actual parse/restore owner. SCV parser session explicitly reports full-reparse fallback, and cannot be promoted to authoritative Simple AST reuse.
- `src/lib/common/task_runner/{scheduler,journal}.spl`, `src/app/buildrunner/runner.spl`, TestRunner coordinator: reuse existing task IDs, journal and parent-owned completion. A helper lease cannot prove the entire runner is live.

## Compatibility decisions

1. **Full physical bootstrap authority:** recommended compatible implementation is an explicitly captured source projection, then the unchanged full audit on that projection. Capture HEAD/index (including intent-to-add/deletions), working and unsaved bytes, discovery/config inputs, generated/alias/runtime/tool dependencies. Cache directories live outside. Pros: preserves current authority meaning and bounds unrelated cache growth. Cons: requires complete observed input closure and exact captured-overlay materialization. Effort: substantial owner integration. Alternative versioned source-only authority could be smaller but changes the contract and requires user selection; it is held. Never silently prune ignored directories.
2. **Summary names and wire data:** keep canonical `.tld` / `__init__.tld` and PackageTldrHeaderV1. Adapt private `.tldr` companions through explicit versioned producer/reader compatibility under existing owners. Pros: preserves callers and avoids two freshness authorities. Cons: three cold producer/validator consumers need coherent changes. Effort: medium-to-large compiler integration. Replacing the canonical format wholesale is not selected.
3. **Optional asynchronous checks versus qualified success:** no conflict. Developer binary may be ready while optional work is pending; CI/release/TestRunner success waits for all mandatory exact-generation receipts. Preserve separate result fields and terminal states.
4. **Conservative fallback versus parse-once:** initial full invalidation is allowed, but a retained authoritative parse for a frozen generation must feed TLDR and compilation. Unsupported syntax/boundaries may reparse after a miss; never reuse a stale flat-pool alias to avoid counting work.
5. **SDN/binary versus diagnostic JSON:** production source metadata, queue state and receipts use the selected existing SDN/binary owners. Private Python/JSON request tooling does not become the production control plane.

## Work packages and dependency order

| Work package | Concrete deliverable and owner | Acceptance gate | Status |
|---|---|---|---|
| WP0 P0 | Pin actual source/provider, baseline counters and current call graph | Cold/warm outputs and diagnostics; resource envelope; no repeated green runs | Partial evidence, no admitted full baseline |
| WP1 P0 | Common SourceChange types/validator; existing codec service, strict binary/SDN frames | Exact bytes, old/new roots, sequence, corrupt/critical frames, bounded allocation | First pure primitive being authored; codecs/service missing |
| WP2 P0 | IDE transaction, Spipe observed-write, SCV editor adapters | Equivalent transitions yield same semantic batch digest; actor metadata separate; outbox recovery | Missing |
| WP3 P0 | Existing SCV schema migration and WAL integration | v1 readable; replay/torn tail; no false fresh defaults; one lease owner | Missing |
| WP4 P0 | Package TLDR complete verifier and actual compiler bridge | Source/header same generation, absent header miss, HIR ABI equality, full coverage | Private bridge work active, native unqualified |
| WP5 P0 | Git notes/SCV receipt association and status/history | Exact tree/config/scope, CAS existence, expected-old ref, no source rewrite | Missing |
| WP6 P0 | Existing journal post-build scheduling/TestRunner join | Binary retained on late failure; remaining only; stale job cannot stamp new generation | Missing |
| WP7 P1 | Authoritative incremental parser and retained AST ownership | Byte-region fresh-parse parity, error boundary fallback, reset-safe lifetime | Actual full parse cache controls limited; regional reuse incomplete |
| WP8 P1 | Exact semantic read sets and static universe closure | Private edit cutoff; public/generic/aspect/negative membership propagation | Types exist, consumer coverage unproven |
| WP9 P1 | Compatible hybrid/directory/packed SMF | Same semantic sections/link behavior and corruption handling; no duplicate storage | Existing section APIs, cross-layout qualification missing |
| WP10 P1 | Selective bootstrap and shared worker/provider admission | Reachable hello closure only; producer/runtime provenance; no duplicate build | Authority projection and runner repair active; full build blocked |
| WP11 P2 | Remote cache/retention/optional explicit async commit | Trust-domain validation, safe GC, conditional commit and authorized sync | Missing, depends on local complete vertical slice |

Implementation order follows WP0→1→2/3→4→5/6, then independent WP7–10 correctness gates, then WP11. Existing bridge work can proceed in parallel without redefining the shared edit owner. Root is merge/runtime-launch owner; this lane owns common edit validation and the matrix; other active lanes retain their private files. No additional sidecars.

## Performance and formal obligations

Cold cost is separate captured bytes + enumeration/hash + authoritative parse + TLDR encoding + HIR/MIR/object/link + startup/scheduling. Warm cost is identity/receipt admission + actual delta work. Each source capture/hash and tree-proof hash is counted once per admitted generation, not once per target. Warm zero body parse/lowering/emission is conditional on valid retained coverage and unchanged complete keys. Input byte lower bounds preclude a universal 0.1-second claim.

Measure median/p95, CPU, peak RSS, bytes, file opens, parse/restore/emission counts, miss reasons, note latency and queue critical-path overhead on pinned cold bootstrap, unchanged build, hello, comment/body/API/new-module/static flip, multiworktree/high concurrency and remote cases. The proposed <10 ms p95 queue target is unmeasured and must not override correctness. Pure array/dictionary registry and allocation costs must be measured on the linked pure provider, not inferred from seed behavior.

Formal safety: one active owner per immutable key; no foreign result publication; no source/header/AST generation mixing; all read-set/membership/config dependencies included; parser boundary errors fail closed. Liveness only under fair scheduling, adequate resources, provider termination, and parent-confirmed dead-owner reclamation. Pure model checks do not upgrade to ModelProven/SourceRefined without the actual engine and source refinement witness. All such proof status remains NOT_CHECKED.

## Evidence update for this plan revision

The first new V3 index diagnostic consumed one of three cycles: nine structural cases executed, seven passed and two failed on the seed byte-array iteration fixture path; no skips or drops. The independent full-topology job timed out at 90 seconds with no counted verdict, so executed/pass counts are unknown. The Job closed. This does not establish native/provider/performance qualification or whole-topology success. The original SCV thirteen-case lane remains closed; its eight passes and five setup failures are not replayed.

The first SourceChange primitive cut has fifteen unexecuted cases. Its original `app.spipe.testing` fixture import has no matching module in the selected release. A preserved successor fixture uses the real `std.spec` owner before any preparation or execution. Production primitive source is unchanged; no alias module was added.
