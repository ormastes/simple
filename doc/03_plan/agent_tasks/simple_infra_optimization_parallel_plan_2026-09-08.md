<!-- codex-design -->
# Simple infrastructure optimization: parallel-agent development plan

**Date:** 2026-09-08
**Status:** Active rolling plan
**Merge owner:** Astra (`/root/jit_memory_reaudit`) for this revision; the root
coordinator owns scheduling and integration decisions
**Final reviewer:** Astra, incorporating Sol ownership/concurrency and
evidence/status audits (both received 2026-09-08)
**Concurrency limit:** four sessions total: one coordinator and three workers;
reviews and sidecars consume worker slots, not extra slots

**L7 interface baseline:** [three-payload interface freeze](../../05_design/three_payload_interface_freeze_2026-09-08.md).
DTO/port names and owner files are reserved there. Astra/root G0 review must
finish before further parallel L7 implementation; no implementation sublane
was started by this freeze task.

## Goal and completion boundary

Deliver measured improvements to runtime performance, interpreter/compiler
startup, compiler/interpreter/generated-binary memory, dynlib/aspect loading,
and pure-Simple ownership. Compare equivalent Simple behavior with C, Go, Rust,
Python, and Bun through executable SSpec evidence.

The coordinator schedules, resolves ownership, reviews diffs, and verifies
evidence. Worker agents research, edit, and run their owned checks. No lane may
claim production performance from the Rust bootstrap seed. Completion requires
an admitted self-hosted Simple artifact and retained p50/p95/RSS/binary-size
evidence; structural and bootstrap-interpreter results remain explicitly scoped.

## Shared contracts before fan-out

- Semantic object names: `PortableBase`, `PortableOptimized`, `.tld`,
  `__init__.tld`, `.rr`, and `.sio` retain their compiler-cache definitions.
- LSP worker name: `LspQuerySessionV1`; it owns bounded framed transport and
  never prints query implementation output onto MCP protocol stdout.
- Parallel result flow: frozen/copy input → child-created result → bounded
  transport → coordinator validation → deterministic owner-side commit.
- Sidecars use existing test helper names. New scenario steps describe user or
  operator behavior; missing helpers fail with `fail(...)`, never placeholder
  passes.
- Each lane preserves unrelated dirty files and publishes an owned-file list,
  acceptance command, result, limitations, and retained evidence paths.

## Ten lanes

| ID | Lane and model | Owned scope | Required result | Estimate |
|---|---|---|---|---:|
| L1 | Self-host admission — **Astra** | Pure-Simple MIR Result provenance; narrowly scoped non-vendor Rust bootstrap producer repair; Stage 2 evidence | Correct aggregate field selection; rebuilt disassembly; admitted candidate without guard bypass; Rust remains bootstrap-only | 1–3 d |
| L2 | Runtime hot paths — **Sol**, Astra review if ownership/concurrency is unclear | Pure-Simple runtime algorithms, allocations, syscalls | One measured or counter-proven work reduction with semantic parity | 1–2 d |
| L3 | Interpreter/compiler startup — **Sol** | Module discovery/loading, eager imports, startup routing | Remove repeated scans/eager work; focused startup counters and tests | 1–3 d |
| L4 | Memory lifecycle — **Astra** | SMF/JIT mappings, arenas, caches, eviction/retirement | Failed-release retry safety; bounded retention; RSS/lifecycle evidence | 1–3 d |
| L5 | Generated-binary closure — **Sol** | CLI/MCP/LSP capsule/import closure | Remove avoidable eager units; report exact closure-unit/source-byte delta; native bytes only when admitted | 1–2 d |
| L6 | Dynlib and aspect dynload — **Astra**, Sol review | Provider loader, SMF/native variants, aspect callback origin | True mapped payload execution, pin/quiescence, typed call boundary, unload safety | 3–7 d |
| L7 | Physical summary compilation — **Astra** | `.spl/.tld/__init__.tld`, coordinator `.rr`, portable `.sio` | At-most-three worker payload reads; RR-driven affected-file scheduling; macro/trait/aspect closure correctness | 7–14 d |
| L8 | Pure-Simple database migration — **Sol**, Astra on durability | Context SQL adapter, importer staging/publication, PureDatabase recovery | Explicit one-way verified import; no silent SQLite/PureDB confusion; default switch only after recovery gates | 2–5 d |
| L9 | Persistent LSP queries — **Astra** | `LspQuerySessionV1`, result-returning query adapters, bounded child lifecycle | One lazy worker/session; exact-source outline cache; no unsafe mtime-only answer cache | 3–6 d |
| L10 | Cross-language SPipe profiling — **Sol** | Comparison fixtures, collector, raw evidence, generated manual | Equivalent checksums/features; warmup + ≥15 samples; p50/p95/CPU/RSS/artifact identity for every available peer | 2–4 d after L1 |

## Rolling waves: dependency-ready queues

Root schedules and verifies; it is not a fourth implementation worker. Current
workers are Astra `/root/jit_memory_reaudit`, Sol `/root/alias_sort_owner`, and
Sol `/root/pure_simple_migration_candidate`. Session names do not grant ownership
of every file; explicit handoff precedes overlapping work. Additional
Spark/Haiku/Sonnet sidecars: **N/A** under the hard four-slot cap.

| Worker queue | Rolling order | Independent work while blocked |
|---|---|---|
| Compiler/cache — Astra | L1 → L4 → L7 → L6 → L9 | Contracts/regressions; L6 loader/pin/quiescence can precede L7, but portable-object integration waits |
| Runtime/storage — Sol | L2 → L3 → L5 → L8 | Advance from completed receipts to importer/recovery prerequisites; do not rerun green leaf checks |
| Verification/evidence — Sol | L10 peer-only → independent review → non-overlapping L8/L7 support → L10 admitted Simple | Negative cases, manual/evidence audit and handed-off adapters; no Simple production rows before L1 |

Refill each finished slot with the highest dependency-ready bounded task. There
is no global barrier between waves. Owner affinity serializes overlapping
Astra compiler/loader and Sol runtime/database scopes, while independent files
can proceed under explicit ownership. Reviews count against the same cap.
Compiler jobs also have CPU/RSS budgets: three agents are not permission for
three competing full bootstraps or writers to one target/cache directory.

| Wave / gate | Critical work | Parallel useful work | Exit |
|---|---|---|---|
| A — admission unblock | L1 typed text-owner repair and isolated canonical Stage2 admission now PASS; retain admitted snapshot without deployment | L8 native-store/read-only prerequisites; Sol evidence review | Stage2 gate achieved; full Stage3/full-CLI qualification remains separate |
| B — owner correctness | L4 release retry qualification; L7 mutation-scoped epoch authority and exact packer rejection checks | L8 importer; remaining L2/L3/L5 locality work | No stale-epoch publication or failed-release ownership loss |
| C — sealed compilation | L7 physical codecs, restricted worker, complete witnesses and RR coordinator | L6 loader/quiescence and generation invalidation | Actual two/three-payload reads, semantic parity, coherent commit |
| D — reusable execution | L6 direct nested mapping and portable-object integration; L9 persistent worker | Independent crash/cancellation and peer checks | L9 semantic answer reuse only after L7 completeness |
| E — production evidence | L10 admitted Simple/available peers and compiler/lib/MCP/LSP gates | Review retained evidence, not noisy concurrent benchmarks | Required profiles pass; unavailable tools/targets stay explicit |

L8 cannot switch defaults merely because v2 recovery and facade-carrier import
passed. Native SQLite needs a read-only source contract; default admission must
preserve source bytes, stage/destination identity and old-store refusal.
L9 can stage bounded transport before L7, but semantic answer caching requires
membership, absence, macro, trait, aspect, configuration and overlay generations.
L6 retains native/device catalogs, ABI and pin owners.

## Historical status at plan creation

- L1: root direct-call Result-shape correction passes focused 3/3; rebuilt
  candidate and corrected disassembly remain.
- L2/L3: active worker lanes; several earlier quadratic scans and repeated path
  probes are already fixed.
- L4: nested SMF failed-release retention implemented; latest header correction
  remains behaviorally unverified after the session iteration cap.
- L5: LSP/MCP closure reduced by two module units / 2,213 source bytes; one shell
  process per roots/list request removed; focused 2/2 passes.
- L7: architecture exists; production physical summary path is not implemented.
- L8: cross-process recovery passes 2/2 and atomic publication is byte-identical;
  importer source-row/stage lifecycle remains.
- L10: C/Rust/Python peer-only 15-sample evidence exists; Simple is unadmitted,
  and Go/Bun are absent from the current host.

## Current evidence ledger — Astra merge with two Sol audits

This 2026-09-08 ledger supersedes the historical status rows, not the retained
artifacts. Counts are scoped worker/coordinator receipts corroborated by source,
specs and reports; unavailable raw execution remains a limitation. Contract
tests do not prove physical IO enforcement or production performance. Worker
message section numbers are not the L1–L10 lane IDs.

| Lane | Implemented / retained evidence | Open qualification |
|---|---|---|
| L1 | Result provenance and typed text-owner repairs independently reviewed. Isolated rebuild exit 0, 833 compiled/0 failed, canonical Stage2 sanity/receiver/positional route PASS and admission-v2 `status=admitted`. Disassembly verifies content slot 2 and one four-name array→promote→shallow-free with preserved result. A single guarded canonical resume was made from exact Stage2 SHA `319c7bd2...`. Frozen lookup repair `1d138f87...` plus focused spec `240b7b3d...`: source check PASS and 8/8 PASS | Stage3 FAIL remains the last qualification receipt: `848f626638b` moved importer lookup from the frozen registry owner to a transient lowerer Dict; the repair restores only `module_surface_registry_index` and proves hostile cache independence. Astra review was twice scheduler-refused. `module_surface_index_allocation_guard_spec.spl` is unchanged and separately stale 0/2. First-module re-export traces remain a separate risk. No rebuild/retry or Stage3/Stage4 provenance/full CLI/test runner |
| L2 | CMR quadratic-work removal: structural 8/8 and bootstrap behavior 13/13. SDN key sort/materialization 2/2; documented 256-key byte materializations 65,280 → 256 | Production time/RSS; operation-count reductions are not latency ratios |
| L3 | Indexed-deferred lazy spec 5/5; directory lookup 10/10 bootstrap-functional. Candidate retirement now removes stale selective/name/set slots and preserves active registration-order wildcard candidates; stable-filter/structural retirement checks 3/3 and structural performance contract PASS | Actual imported-global scan oracle failed 0/3 under the known bootstrap stale-global-array issue and is not valid runtime evidence. Production scan counts, startup/RSS and integrated invalidation remain |
| L4 | Nested SMF failed-release retention; later independent `None_` correction and refusal/accounting spec 3/3 bootstrap-functional. Astra reconciled overlapping cache/mapper non-positive-extent checks without behavioral edits. Lint retention 2/2; 1,024 occurrences → one retained identity | Current zero-address fixture returns at cache precheck: no executed positive-map close-failure or real kernel unmap/RSS evidence. Valid close-before-accounting remains structurally reviewed; no rerun of green scenarios |
| L5 | Closure reduction two modules / 2,213 source bytes, focused 2/2; one roots/list shell process removed. Canonical logical-path renderer 1/1; reserved `namespace` source contract passes. Later integration 2/3 exposed co-compiled duplicate `make_tool_result` selection; source now uses unique status-bearing helper | Latest response-helper and escaped-payload expectation patch remains unverified after bounded cycle cap; one explicitly scheduled merge-owner integration check is pending. Native size/startup and integrated smokes remain open |
| L6 | Dynlib 2/2 and aspect 25/25 bootstrap-functional. Legacy pack index validates bounded header/directory SHA-256; same-size rewrite regression included in 8/8 PASS. Optimizer symbol index 2/2; required-capability legacy rejection has structural proof | Direct nested mapping, production catalog wiring, immutable generation/whole-pack identity, capacity and pins/quiescence remain. Legacy lookup still performs bounded index IO. Capability-bearing optimizer admission unavailable; new negative Simple spec not executed |
| L7 | V1 DTO 4/4; packer 4/4; mutation-scope model 7/7. Common cycle-3 13/13 (133804 ms), frontend 2/2 and C 5/5 retained. F6 PASS. F7 cycle-3 links/anchors, current 13/2/5 manuals and nonempty rendering accepted; focused 1/1 (496 ms), docgen 3/3 complete/zero stubs retained. G7 R1–R4 fail-closed repair PASS, including closed recovery; writer check, Simple 7/7, seven-scenario manual and unchanged Rust 2/2 retained | PR-A–E approval readiness FAIL. F7 existing renderer swaps labels and omits branch edges; diagram semantics remain wrong. G7 tests exercise closed public negatives, not admitted-host/positive semantic behavior. Concurrent lexer/pending hunks preserved. Exact isolated dependencies/diffs and failed compiler/lib/core/native gates remain; G5–G8 production activation unavailable. Final cycle-3 cap reached |
| L8 | PureDB v2 length+SHA and record/cell framing: 10/10 in-process, 3/3 independent-process. Classifier 2/2; prior publication 2/2. Explicit facade→v2 importer 2/2 in-process + 1/1 independent-process validates ordered rows, source preservation, staged/destination bytes and existing-output refusal | Bootstrap-functional facade carrier only. Native SQLite refused until read-only open contract; default unchanged. Publication assumes serialized caller ownership, not cross-process no-clobber. v1 cannot prove historical delimiter integrity |
| L9 | Bounded-command/path memoization 5/5. Stdout-free DocumentHighlightResult adapter has direct PASS; CLI parity fixture corrected but unverified after cycle cap. Tagged transport/framing/timeout contract 4/4 | Persistent worker remains blocked by runtime ABI: empty stdout conflates would-block/EOF/error, stderr is not drainable, reads caller-unbounded, no tagged close/reap. Adapter independent review pending; L7 completeness gates semantic answer reuse |
| L10 | SPipe/peer gates 3/3; unchanged C/Rust/Python peer-only 15-sample raw evidence. Bounded host discovery confirms Go/Bun absent and binds the exact admitted compiler-only Stage2 candidate. New availability report and focused evidence spec preserve explicit unavailable rows and prohibit fabricated/substitute timings. Single Stage3 attempt has complete guarded timing/RSS/config receipts | No new timings: canonical Stage3 failed before producing a candidate/provenance, so full CLI/test-runner and Stage4 are absent. Focused spec reached its three-cycle cap with cycle-3 output truncated and is not claimed green. No Simple/Go ratio or “slightly slower” claim; repair HIR importing-surface closure plus unequal-work/startup defects and matched outputs/features |

Cache cross-cutting qualification remains **partial 5/9**, not a passed
service. CAS/journal remain authoritative; DB remains rebuildable projection.
The underlying cache writer still has a validation→append epoch race. The new
closure publisher now refuses before CAS staging because mutation-scoped
authority is unavailable; this prevents that route from claiming publication,
but does not repair the writer or make the service passed. Another readiness
check cannot substitute for mutation-scoped owner/host authority.

Evidence anchors:

All `doc/09_report/**` paths cited anywhere in this rolling plan are
local/historical untracked receipts unavailable as repository evidence. They
record context only and cannot satisfy an admission, production, or acceptance
gate. Likewise, `cache_writer_mutation_scope.md` is local/historical and
unavailable; the applicable disabled-authority contract is host-only validated
`CacheCommitFrameV1` commit, durable journal before `CacheCommitReceiptV1`, and
no authority from readiness, caller-filled receipts, or legacy
`result_manifest_put`.

- `doc/09_report/result_payload_provenance_rust_bootstrap_fix_2026-09-08.md`
  and historical `doc/09_report/result_payload_provenance_stage2_rebuild_2026-09-08.md`;
  corrected candidate: `doc/09_report/result_payload_provenance_qualified_stage2_gate_2026-09-08.md`.
- `doc/09_report/transient_surface_name_owner_contract_2026-09-08.md`.
- `doc/09_report/transient_surface_name_owner_stage2_gate_2026-09-08.md`.
- `doc/05_design/three_payload_interface_freeze_2026-09-08.md`;
  `doc/05_design/cache_writer_mutation_scope.md` (model 7/7, native unavailable).
- `doc/09_report/compiler_sections_6_8_astra_admission_review_2026-09-08.md`;
  `doc/08_tracking/bug/cache_writer_epoch_validation_append_race_2026-09-08.md`.
- `doc/08_tracking/bug/compiled_module_registry_quadratic_exports_and_lookup_2026-09-07.md`;
  `doc/08_tracking/bug/smf_cache_failed_release_ownership_2026-09-08.md`.
- `doc/08_tracking/bug/simple_lsp_mcp_virtual_read_gateway_closure_2026-09-08.md`;
  `doc/08_tracking/bug/three_payload_compile_contract_missing_2026-09-08.md`.
- `doc/08_tracking/bug/aspect_pack_index_cache_generation_ownership_2026-09-08.md`;
  `doc/08_tracking/bug/simple_lsp_mcp_per_query_compiler_process_2026-09-08.md`.
- `doc/05_design/lib/database/pure_database_disk_v2.md`;
  `doc/08_tracking/bug/context_sql_pure_database_migration_2026-09-08.md`.
- `doc/09_report/cross_language_peer_feature_core_2026-09-08.md`.

## Three-payload and object compatibility gate

Retain one compiler/query/codec chain and existing `PortableBase`,
`PortableOptimized`, `.sio`, native SMF/object and device-bundle ownership.
Warm worker payloads are `.spl`, prior module `.tld`, and `__init__.tld`; cold
new-file compilation has two because its prior header does not exist yet.
This ends at frontend semantic/common-object production: process startup,
target lowering, linking and runtime initialization have separate read counts.

Completeness is not one-folder locality. Referenced features may live elsewhere
if their consumed semantics are packed in verified indexed sections.
Macro/CTFE and consumed generic/default-trait bodies are embedded for execution;
ordinary concrete trait calls and call-only aspects carry signature, effects,
selection/order and symbolic immutable callable/object identity without opening
implementation bytes. Inlining/body observation needs an embedded body or a
typed multi-payload fallback, never a hidden fourth worker read.

`.rr` only schedules affected owners in the coordinator; it does not own or
inject macro bytes. New/removed features and files update membership/candidate/
absence witnesses; the absence of an old reverse edge cannot prove that no
consumer is affected.
Commit outgoing reads, RR deltas and summary/object roots coherently; consumer
additions do not change producer semantic identity. Test positive, negative,
cold, overflow, scope-change and corruption cases through actual restricted
handles and measured opens/bytes, apart from preparation/control-plane work.

## Owner-result and conflict policy

### L7 frozen dependency order and exact scopes

The detailed DTO field ledger and port signatures are in the interface baseline;
this table is the scheduling/ownership authority. New source paths are proposed,
not already implemented. No two agents edit shared common DTOs concurrently.

| Gate / owner | Exclusive file scope | Depends on / acceptance |
|---|---|---|
| G0 — Astra contracts | `src/compiler/00.common/cache_contract/{physical_tld_v1,package_init_tld_v1,semantic_query_read_manifest_v1,reverse_reference_shard_v1,portable_object_ref_v1,generation_manifest_v1,three_payload_compile_v2,three_payload_worker_v1}.spl`; interface/plan docs | Root+independent review of names, fields, golden fixtures, strict digest/version migration; retain current V1 bytes/tests |
| G1 — Sol codec | `src/compiler/10.frontend/cache_artifact/{physical_tld_codec_v1,public_summary_projector}.spl`; mirrored codec/projector specs | G0; binary indexed round-trip, exact original-object identities, optional/mandatory field preservation, no second extractor |
| G2 — Sol RR | `src/compiler/80.driver/cache/reference/reverse_reference_coordinator_v1.spl`; mirrored reference specs | G0; forward reads + membership/absence → dirty query owners, old/new domains, deleted edges, zero-match and SCC cases; semantic/AOP leaves only via explicit handoff |
| G3 — Astra authority/IO review | `doc/04_architecture/cache_writer_mutation_scope.md`, matching detail/model; proposed `src/compiler/80.driver/cache/worker/three_payload_worker_io_v1.spl` | G0; host implementation scope remains separately gated; real confinement/counters, no caller-issued IO proof |
| G4 — Astra packer | `src/compiler/80.driver/cache/closure/three_payload_closure_packer_v2.spl`; mirrored V2 packer specs | G1+G2; immutable source + optional original prior TLD + newly sealed init TLD; no fourth bundle; complete semantic/witness closure |
| G5 — handed-off verifier | New strict worker integration specs and isolated fixtures only | G3+G4; actual cold2/warm3 distinct inputs, zero external/RR worker reads, measured bytes, denied escape and full-source parity |
| G6 — Astra portable owner | `src/compiler/20.hir/{hir_codec,portable_object_profile_v1}.spl`; mirrored portability specs | G5+existing HIR/SMF verifier; Base/Composed refs, symbolic target semantics, no duplicate IR or native-object confusion |
| G7 — Astra publication | `src/compiler/80.driver/cache/publication/three_payload_generation_publisher_v1.spl`; writer/journal changes only by serialized handoff | G2+G5+G6+admitted mutation authority; immutable blobs first, journal commit before visible action lookup/DB projection; real revoke/crash/recovery/pin tests |
| G8 — root schedules, Sol verifies, Astra reviews | Integrated semantic/performance fixtures, reports and approved rollout configuration | G7+admitted Stage2/Stage3 matrix; no default until all required evidence, isolated review/PR gates pass |

Post-repair source and focused execution close the concrete F2/F5 integrity and
allocation defects. Final Astra correction review now passes those changed
paths against common 8/8, frontend 2/2, and driver 5/5 bootstrap-functional
receipts. This does not close semantic generation authority, complete-domain
scheduling, or production G5–G8. The following dependency slices remain
preparation order, not approved PRs:

1. **PR-A — common contract/codec:** G0 common DTOs, physical TLD framing,
   nested aggregate budgets, common specs and mirrored manual. This is the
   wire-format authority and must land first.
2. **PR-B — frontend adapter:** G1 bounded frontend decode/semantic binding and
   focused specs/manual; depends on the exact PR-A common API and bytes.
3. **PR-C — fail-closed driver assembly:** G2 RR normalization/refusal, G3
   unavailable worker port, G4 exact aggregate packer verification, unavailable
   publication/portable-HIR ports, and the 5/5 integration spec/manual; depends on PR-A and
   PR-B. It must not advertise G5–G7 success.
4. **PR-D — production execution authorities:** restricted broker IO (G5),
   semantic portability (G6), then mutation-scoped durable publication (G7),
   serialized in that order and each independently reviewed; depends on PR-C.
5. **PR-E — rollout and performance (G8):** integrated recovery, semantic and
   performance evidence plus admitted Stage2/Stage3 and broad regression gates;
   depends on PR-D. Default activation remains forbidden before this slice.

**Current PR approval readiness: FAIL for A–E.** The latest Astra review is
`Final capped cycle-3 review — F7 and G7` in
`doc/09_report/three_payload_integrated_astra_review_2026-09-08.md`; its exact
hashes/verdict supersede earlier optional-field, dependency-inventory, failed C,
and enabled-verifier observations.

- A's common receipt is now source check plus **13/13**, exit 0, **133804 ms**
  (bootstrap-functional). Explicit TLD2 framing
  retains optional bytes losslessly, rejects mandatory semantics and validates
  extension ranges/budgets before extension retention; strict TLD1 is preserved.
  **F6 PASS at the cycle-3 snapshot:** original-buffer, end-confined preflight
  applies caller section/per-section/aggregate decode limits, raw profile and
  stored/decoded equality, section ownership/index, contiguous bounded ranges,
  and exact payload coverage before the full core slice. The valid 256 KiB
  core/one-byte-bound case, stored 256 KiB/decoded 1 malformed case, zero-section
  nonempty-payload case, and source/helper pins are accepted. This is bounded
  structural and bootstrap-functional evidence, not zero-copy or measured RSS.
  The common manual now contains the final malformed-core steps. F7 cycle-3
  corrects the REQ-CSM-006 destination and renders nonempty diagrams, but their
  node labels and branch relationships remain inaccurate.
  Frontend/driver TLD2 consumption is not claimed.
  The exact untracked `three_payload_compile_v1.spl` prerequisite is
  now documented; include its owned file or exact prerequisite head.
- B's **2/2** receipt remains scoped functional evidence. Its untracked
  `three_payload_semantic_closure.spl` and modified `cache_artifact/__init__.spl`
  dependencies are now documented, but still require exact included files/hunks
  or prerequisite heads alongside repaired A.
- C's current corrected spec/manual supplies the canonical portable verifier
  identity and tests unavailable public semantic admission independently of
  physical worker/native-loader/publication authority. The coordinator reports
  a new **5/5**, verdict OK, 5860 ms; this supersedes the transient 0/5 as current
  functional evidence, without diagnosing that older parse observation. Exact
  isolated A/B/worker/portable owner handoffs and shared gates remain required.
- F7 cycle-3 Astra review accepts visible primary scenarios, folded source,
  current provenance/date, all twelve requirement destinations and 13/2/5
  source-matching manuals. Concurrent lexer/pending hunks remain preserved.
  The existing renderer now supplies six ASCII body lines per manual, and the
  updater directive is absent. Retain generator check PASS, focused 1/1
  (496 ms), and docgen 3/3 complete/zero stubs/200 documentation lines.
  **F7 remains FAIL:** sorted label order is applied to topological node order
  by the renderer, mislabelling nodes; LR draws only same-row edges and omits
  branches. Common/driver visibly show compiler -> std instead of the SDN's
  spec -> std/compiler relationships. The one-import fixture's nonempty-line
  assertion misses this. Exact hashes and source cause are in the final review.
  The final cycle-3 cap is exhausted; record the remaining failure and stop.
  They also need retained knowledge-selection and requirement traceability; applicable
  compiler/lib/MCP/LSP checks, MCP stdio/core-runtime/native smoke receipts;
  numbered-artifact/direct-env working and staged audits; the zero-executable-
  spec documentation layout check; and isolated tracked/untracked diffs with
  exact dependency/remote heads and required checks reviewed before approval.
  The existing bootstrap-functional passes do not qualify self-hosted runtime
  production behavior. Additional package checks apply if packaging changes.

Current D source now checks worker policy before prepared decoding/provider
copying and exposes logical in-memory read counters without physical-open or
peak-allocation claims. Its portable predicate rejects untyped/nonliteral
expressions and public semantic admission remains false. These static changes
supersede the earlier F9/F10 source observations; they do not establish complete
G5/G6 correctness or authorities. Retain exact owner handoffs and independent
D evidence, full Base/Composed SMF/stage/differential gates, then G7 publication.
No narrow subset or closed-port test establishes production qualification.

Reported audit status: direct-env working/staged pass, numbered-artifact staged
pass, numbered-artifact working fail on unrelated PureDB version artifacts,
and zero executable specs under `doc/06_spec`. These are scoped receipts;
empty staged state does not satisfy future isolated-PR staged gates.

PR-D implementation remains sequential across these existing owners:

1. G5: `src/compiler/80.driver/cache/worker/three_payload_worker_io_v1.spl`
   plus the confined broker owner. Require private admitted handles and trusted
   IO receipts, actual cold-two/warm-three input objects, foreign/CTFE/ambient
   escape refusal, truthful IO/allocation measurements, and clean-compile
   semantic/diagnostic parity.
2. G6: `src/compiler/20.hir/{hir_codec,portable_object_profile_v1}.spl`.
   Require Base/Composed SMF semantic profiles, symbolic target layouts and
   effects/body closure, target separation and native-loader refusal;
   serialization round-trip is insufficient.
3. G7: `src/compiler/80.driver/cache/publication/three_payload_generation_publisher_v1.spl`,
   `src/compiler/80.driver/cache/gateway/cache_writer_v1.spl`, and the existing
   `src/lib/common/cache_daemon_host_authority_v1.spl` host boundary. Integrate
   existing journal/CAS and Simple DB server/projection authority. Require
   mutation-scoped commit, real concurrent revoke/commit and retry/crash/recovery,
   no lookup visibility before admission, reader/GC protection, and DB rebuild
   evidence. Reuse the existing DB server; no new database server is planned.

PR-E owns integrated `test/02_integration/compiler/cache/` scenarios and mirrored
manuals, retained semantic/recovery/performance reports, and eventual reviewed
rollout configuration. Require PR-D, admitted Stage2/Stage3 evidence within
supported scope, broad regressions and realistic startup/latency/RSS/binary-size
results before activation. No production gate is satisfied by DTO counts or
closed-port refusal. The final review and exact prerequisites are recorded in
`doc/09_report/three_payload_integrated_astra_review_2026-09-08.md`.

After G0, three worker slots can run G1, G2 and G3 independently. Refill only
dependency-ready non-overlapping scopes; G4–G7 serialize shared compiler owners.
Root schedules/reviews, never becomes a fourth implementation worker. Scalar
aspect/trait calls stay symbolic; executable macro/default/generic bodies stay
embedded in admitted TLD sections; `.rr` remains coordinator-only. A cold prior
header is absent successfully, not synthesized as an input to its own output.

### User-authorized lane completion and PR workflow

The user authorizes pushing completed lanes and approving their PRs. This is
conditional on a clean lane-isolated worktree/branch and scoped PASS evidence:
collect only owned source/tests/docs, inspect exact diff (including untracked
files), preserve unrelated work, complete Astra ownership/semantic review plus
independent evidence review, then commit/push that lane and create/update its PR
using repository sync/verify rules. No publication/release/default switch is
implied by a docs/model PASS. Blocked or partial production gates remain open.

Before approval, inspect the exact remote head, changed files, required checks
and review evidence; new commits require renewed review. If GitHub rejects
author self-approval, record the actual refusal and request an independent
authorized reviewer—do not switch identities or bypass branch protection.
No force-push, unrelated commit, deployment or release is authorized by this
workflow. This plan-edit task performs no commit/push/PR mutation. Root retains
merge/integration control after required review and checks.

Every mutable compiler cache, database file, mapped region, provider generation,
and result catalog has one named owner. Agents exchange immutable reports and
owned patches, not shared mutable objects. Unknown access ranges overlap.
Cancellation never implies child/device completion. Failed unmap, publication,
or admission retains enough owner state for retry and cannot publish partial
success.

The coordinator rejects overlapping edits unless one lane explicitly hands the
file to another. Integration order is contracts/tests → leaf implementation →
adapters → defaults → retirement. Parent commit occurs only after scoped diff
review and the lane's one declared verification run.

## Evidence gates

Each lane must provide:

1. A biting semantic regression and failure-path case with no `pass_todo`,
   tautology, or empty scenario.
2. Exact execution identity: source, compiler/runtime/provider, arguments,
   output artifact, and mode.
3. Retained raw samples for performance claims; warmup is untimed and runtime,
   startup, compilation, and linking remain separate.
4. p50 and p95 wall/CPU, max RSS, binary/closure size, and semantic checksum as
   applicable. Cache hits also report bytes decoded/transferred and queries
   rerun.
5. `git diff --check` for owned tracked files and explicit
   `git diff --no-index --check /dev/null <owned-untracked-file>` for new files.
   Ordinary diff does not inspect untracked content; distinguish normal
   no-index difference exit from whitespace/error diagnostics.
6. Explicit classification: admitted production, bootstrap-functional,
   structural, modelled/emulated, peer-only, unavailable, or failed.

No narrow unit test supports a repository-wide performance claim. Each scoped
criterion runs once; no more than three verify/fix cycles and no rerun of green
checks to occupy an idle slot. Freeze source/toolchain inputs for isolated
builds; do not mutate the measured/admitted closure. One owner writes each
build/cache/output state.

Reserve quiet production sampling windows: pause unrelated builds, tests and
IO-heavy sidecars, retain hardware/load/cache-state metadata, then resume the
queue. Parallel development and isolated performance measurement are separate
modes. Compile-to-portable, dev native, release native and runtime require
separate rows and matched feature/output contracts for Java/Go comparisons.
Keep disabled/local/remote cache profiles and transferred/decoded bytes separate.
Set absolute budgets from admitted M0 baselines, not seed or peer-only times.

After L1,
the final matrix runs cold/warm no-op, local edit, public semantic edit, aspect
change, second target, cache outage/corruption, dynlib load/unload, and idle
retirement. Required compiler/lib/MCP/LSP checks follow the repository verify
policy once overlapping lanes converge.

### Broad lib-check memory regression — 2026-09-08

The one retained `bin/simple check src/lib` run (session `15636`) exposed a
concrete checker memory/performance defect while processing the grouped
`src/lib/nogc_async_mut_noalloc/qemu/` batch (`mod.spl`,
`debug_boot_runner.spl`, and the adjacent baremetal IO closure). The child
remained at 100% CPU and reached an observed RSS of `67,552,916 KiB`
(approximately 64.4 GiB, 52.9% of this host) after 16m38s in that batch, with
no result emitted. The parent had run for 24m13s. A cooperative interrupt did
not terminate the child; the exact child was sent SIGTERM, then the exact
parent PID was sent SIGTERM. The unified command terminated with exit 143 and
was not restarted.

This is a release-blocking broad-check resource regression, not an A-C semantic
failure. Resume work must freeze the exact noalloc/QEMU file manifest, run it
in smaller isolated checker batches with retained time/max-RSS samples, identify
the type/import graph responsible for superlinear retention, and add a bounded
RSS regression gate before restoring the full `src/lib` check. The existing
per-batch 2220s timeout is not an acceptable memory bound.

#### Bounded current-tree investigation — NO-REPRO

The isolated follow-up did not reproduce the runaway and therefore made no
speculative compiler or target-deduplication change. The exact current sorted
`src/lib` batch at indices 5153--5184 contains 32 files, from
`nogc_async_mut_noalloc/memory/refc_binary.spl` through
`nogc_async_mut/oauth/authorize.spl`, including all seven
`nogc_async_mut_noalloc/qemu` files. Its canonical evidence manifest is the
SHA-256 `9ba001786d572882fef20a2d0b61484a07d21a34dc5598740adb4c5d7ec66884`
over newline-delimited `sha256sum <path>` rows in that order.

With a 4 GiB virtual-memory ceiling and a 180-second outer timeout, that exact
32-file invocation completed in 6.01 seconds (user 5.85, system 0.16) at
410,308 KiB maximum RSS. It exited 1 solely for five existing diagnostics in
`tls/handshake.spl`; it did not time out or show unbounded growth. Individual
`qemu/mod.spl` and `qemu/debug_boot_runner.spl` checks peaked at 407,888 and
429,928 KiB, the three named QEMU/IO files peaked at 403,244 KiB, and the full
seven-file QEMU directory peaked at 413,052 KiB. Each bounded QEMU-only check
passed.

The executable resolved from `bin/simple` to
`bin/release/aarch64-unknown-linux-gnu/simple`, SHA-256
`3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`,
mtime 2026-09-06 09:59:11 +0900. It self-reported as a Rust-built bootstrap
seed, so these are bootstrap-functional diagnostic samples, not admitted
production evidence. The original 64.4 GiB observation did not retain an
executable digest, exact ordered source manifest, execution-mode/environment
receipt, or raw RSS samples. It cannot establish a current allocation root.
The next production attempt must freeze those inputs and impose an RSS limit
in addition to the existing time limit; until then the broad-check regression
remains open rather than being marked fixed.

## G7 durable-writer review result — 2026-09-08

The seven-path frozen G7 candidate is **FAIL** under final Astra source review
(`/root/l7_ac_verify_docs/l7_g7_astra_review`). Existing Simple DB/PureDatabase
ownership is preserved, Linux has a bounded lock-gated durable byte primitive,
and C/non-Linux remain unsupported. Public generation publication remains
unavailable with
`verified_cas_generation_kinds_and_gc_reachability_unavailable`; this blocker
must remain until verified CAS kinds and generation-hierarchy GC marking are
admitted together.

The new semantic writer still requires four bounded corrections: **G7-R1/P1**
replay must consult owner-bound durable journal evidence before projecting;
**G7-R2/P1** the separately exported writer must not admit arbitrary raw/missing
CAS digests while its generation capability is closed; **G7-R3/P1** append must
bind the expected journal prefix, not merely its length; **G7-R4/P2** prepared
record fields must match the canonical appended bytes. Exact paths, triggers,
hashes, and source references are in the final G7 section of
`doc/09_report/three_payload_integrated_astra_review_2026-09-08.md`.

Retain the reported Rust **2/2**, four source-check passes, focused spec final
**4/4**, and whitespace pass without rerunning them. They are limited evidence:
the Simple scenarios do not execute the new live writer/recovery boundary, and
Rust tests exercise only host bytes. Add the identified semantic negative cases,
compiled boundary/restart/crash evidence, and the missing canonical spec manual
before another bounded review cycle. No coverage measurement, isolated lane
head, or admitted self-hosted/shared-gate PASS was supplied. G7 and PR-D remain
incomplete; no publication/default switch is authorized by these receipts.

### G7 R1–R4 final capped cycle-3 review

All fourteen final F7/G7 hashes match the coordinator handoff.
**G7 R1–R4 fail-closed repair: PASS, scoped to the disabled boundary.** R1
removes caller-memory authority from commit, R3 binds the host-gated expected
prefix, and R4 binds prepared records to canonical append bytes. R2 is now
closed in recovery: the exported function checks semantic/CAS gates and
unconditionally returns `CacheUnavailable`, with no host read or catalog
rebuild. Raw or missing-CAS frames cannot project through that surface.

Retain writer check PASS, Simple **7/7**, manual **1/1 complete/zero stubs,
70 documentation lines**, whitespace PASS and unchanged Rust **2/2**. New
tests call the real public commit/recovery interfaces and verify absent rows,
an unchanged recovery projection digest, and retention of the original row
when a conflicting object is offered. They use invalid opaque receipts and
`is_err`; these are closed-interface negatives, not independent proof of CAS
gate precedence, admitted-host recovery or enabled nondeterminism handling.
Coverage is unmeasured; compiled semantic-boundary, restart/crash/pin evidence
remains open. The seven-scenario manual matches source but shares F7's omitted
branch arrows. Exact hashes/verdicts are in the integrated report's final
cycle-3 section. No further correction cycle is authorized within this session.

Existing Simple DB/PureDatabase, journal, host and CAS/GC ownership is preserved.
G7 activation remains unavailable on
`verified_cas_generation_kinds_and_gc_reachability_unavailable`: admitted
generation/artifact kinds, generation-hierarchy GC marking, an owner-issued
durable/reachability receipt and integrated authority evidence are still
required. A/B/C/D approval separately remains FAIL on residual F7 where
applicable, exact dependencies/owned diffs, knowledge/requirement receipts and
retained shared gates; D additionally lacks full G5–G7 qualification.

## L8 verified-CAS and GC authority freeze — 2026-09-08

This wave extends the existing verified CAS, action-root journal, reader-pin,
GC and Simple DB/PureDatabase projection owners. It creates no second database,
CAS, journal or persistence server. Publication remains disabled until an
independent Astra review accepts the complete closure and receipts.

### Artifact-kind and schema registry

The five existing `CCH1` schema-1 kinds and their numeric tags remain strict and
unchanged: `source_blob=1`, `compile_snapshot=2`, `public_summary=3`,
`file_ast=4`, `semantic_read_set=5`. New generation objects use the exact
already-owned canonical bytes below; they are not rewrapped or reinterpreted,
because all current generation references hash those exact bytes.

| Kind string | Canonical schema/identity | Admission rule |
|---|---|---|
| `generation_manifest` | `GEN1`, schema 1; `generation_manifest_decode_v1`, byte-identical re-encode, SHA-256 of exact bytes | Required root; every typed child must close |
| `worker_result` | `TPW1`, schema 1; bounded decode, byte-identical re-encode | Fixed interpretation of current `scope_refs`; no arbitrary scope bytes |
| `forward_manifest` | `SQR1`, schema 1; bounded decode, byte-identical re-encode | Authoritative forward reads used for RR rebuild |
| `diagnostic_manifest` | Reserved `DGM1`, schema 1 | Unavailable until a bounded canonical codec exists; opaque diagnostic bytes never admit |
| `portable_hir_object` | Exact HIR codec bytes with `ir_schema=2`, bound `PortableObjectRefV1`, verifier identity and receipt | Reference-aware API only; generic put rejects; remains unavailable while the semantic verifier is false |
| `reverse_reference_shard` | `RRS1`, schema 1; bounded decode and byte-identical re-encode | Derived/rebuildable child; never a forward semantic authority |
| `target_artifact` | Reserved typed root | Unavailable until its existing owner supplies a canonical codec/verifier; no opaque admission |

Unknown kind, schema, mandatory field, noncanonical ordering, trailing bytes,
digest mismatch, missing child, wrong kind for a manifest slot, or unavailable
typed verifier fails closed. Compatibility is exact schema admission, not a
fallback to `CCH1` or an older kind. The CAS registry must expose a stable
registry digest so recovery receipts bind the verifier set used.

Digest policy is kind-aware and registry-bound. The five legacy `CCH1` kinds
retain the existing domain-separated `verified_cas_digest_v1` identity. New
self-framed GEN1/TPW1/SQR1/DGM1/RRS1 objects use SHA-256 of their exact verified
canonical bytes. Portable HIR uses its bound `PortableObjectRefV1.content_digest`
through the specialized verifier. No caller may substitute one digest scheme
for another kind.

### Reachability, pins and recovery receipt

- Reachability identities are `(kind, digest)`, never an untyped digest. An
  admitted action-journal record roots `generation_manifest`; explicit pins and
  active leases root generations, not arbitrary leaf paths.
- A generation traversal verifies the root first, then its fixed typed edges:
  snapshot→`compile_snapshot`, summaries→`public_summary`, scopes→`worker_result`,
  RR refs→`reverse_reference_shard`, forward refs→`forward_manifest`, portable
  refs→`portable_hir_object`, diagnostics→`diagnostic_manifest`, and target refs
  through their reserved typed owner. `catalog_digest` is instead
  bound to the existing PureDatabase/catalog owner receipt; it does not create
  a second CAS or database object. Any unavailable or invalid
  edge makes the closure unavailable and prohibits sweep/publication.
- Marking runs from an immutable pinned root snapshot. No verified-CAS object is
  moved to trash while a generation pin/lease can reach it. A corrupt/missing or
  unverified root aborts sweep; it is not treated as an absent leaf. Trash and
  grace deletion remain two separate phases.
- `VerifiedCasClosureReceiptV1` is owner-issued only after pinned traversal. It
  binds generation/root digest, ordered `(kind,digest)` closure, closure digest,
  verifier-registry digest, pin/epoch identity, accepted journal bytes and
  prefix digest. PureDatabase recovery may project only from a matching durable
  journal receipt plus this closure receipt; caller memory or raw host bytes
  cannot manufacture recovery authority.

### Non-overlapping ownership and evidence

- CAS owner: verified kind registry/dispatch and focused codec/kind negatives;
  no GC, journal, DB or publication edits.
- GC owner: new verified-generation traversal/pin/recovery-receipt owner and
  focused reachability/restart/conflict tests; preserve the concurrently dirty
  legacy `gc/admission.spl`, `gc/fast_gc.spl`, and `gc/mark_sweep.spl` unless an
  explicit handoff is recorded.
- Coordinator: integration and report/plan only. Final Astra review is required
  before any availability flag or publisher path changes.

Candidate handoff: CAS stopped at cycle 3 with focused 5/5 PASS; GC stopped at
cycle 3 with focused 9/9 PASS and a canonical zero-stub manual. Both candidates
are frozen pending independent Astra source review. The review must specifically
cover cross-new-kind digest refusal, DGM1 semantic/lossless adequacy,
known-unavailable path leakage, complete typed GEN1 traversal, every pinned and
leased root, non-constructible durable authority, and receipt-only recovery.
No green focused command is to be rerun. A root-invoked docgen path-normalizer
duplicate was removed; canonical generation from `test/` is retained as an F7
tooling defect, not L8 authority evidence.

Independent review scheduling is currently blocked: fresh and reused Astra
requests both returned `agent thread limit reached` after the implementation
owners released. Retain CAS/GC as unapproved frozen candidates; focused green
receipts do not authorize availability or publication.

A 2026-09-09 retry to spawn the exact requested Astra xhigh combined review
again returned `agent thread limit reached`. This repeated scheduler refusal is
not a static-review verdict: L8 remains unapproved, frozen at the recorded
hashes, and every availability/publication flag remains false.

## L11 optimize/SPipe knowledge handoff — 2026-09-09

The repository optimize skill now includes a bounded evidence-admission and
failure-attribution section derived from the retained L7/L10/broad-check
receipts. It requires frozen executable/source/runtime/config/tool identities;
process-group wall and RSS caps; honest `NO-REPRO` handling; exact ordered
grouped-batch manifests distinct from per-file samples; separate semantic,
physical, worker and publication metrics for three-payload work; cache authority
before speed; independent build-executor/output-target identities; immutable
phase admission; and peer comparability with explicit unavailable rows.

The coordinator-owned insertion is one section in
`.codex/skills/optimize/SKILL.md`; the file already contained extensive
concurrent optimization guidance and that work was preserved. Final whole-file
SHA-256 is `b0eff26b7420deaf76149d248a5c4c51d59513cc01abb44b9f84b07371203651`.
One formatting/whitespace check and all three referenced report/plan link-target
existence checks passed. This documentation update makes no performance or
readiness claim and ran no compiler/runtime benchmark. No commit or push.

## L3 compiler/interpreter startup focused receipt — 2026-09-09

The frozen matrix distinguishes the production Rust seed (`3d120a6f...`),
admitted compiler-only Stage2 (`319c7bd2...`), and unavailable Stage3/Stage4
full CLI. Seed `check` measured about 2.94–2.96 s p50 and about 395 MiB peak RSS;
query measured about 0.71–0.72 s p50 and 153–154 MiB. Stage2 help/version
measured 4.7–5.0 ms but cannot supply check/query.

One pure-Simple query fix replaces the 49-file `app.io.mod` compatibility-hub
import with exact leaf file/dir/env owners. Source check and focused spec passed
(7/7). Candidate query p50 is 451–452 ms (36.46–37.13% lower), peak RSS
117,732 KiB (24.73–25.57% lower), and filtered syscalls fell 9,261→5,025.
Exact provenance, raw samples, hashes and caveats are in
`doc/10_metrics/startup/l3_compiler_interpreter_startup_2026-09-09.md`.

This is seed-hosted interpreter evidence, not self-hosted/Stage4 qualification.
The orchestration transcript has exact argv/environment/watchdog nesting, but
the raw metrics directory lacks an immutable pre-run command/environment
manifest, so the filesystem evidence cannot independently prove comparability.
No second optimization, broad check or evidence rerun was attempted. Freeze
pending Astra and a later manifest-bound qualification; no commit or push.

Astra final status: **WARN**. The leaf-import optimization is narrow semantic
PASS/approval-ready; hashes, arithmetic and query output parity match. Startup
percentage evidence remains provisional, and broad L3/self-hosted performance
readiness is not approved without the missing immutable protocol manifest.

Isolated delivery was prepared from `origin/main`
`86471c7620052827442a1cfb375b6c720507e522` in preserved worktree
`/tmp/simple-l3-query-pr-JWyGDM`, branch
`codex/l3-query-leaf-io-20260909`. Local commit `d9a9392875d` contains exactly
the approved two paths (11 insertions, 1 deletion); its valid bootstrap-
functional focused run passed 7/7. The isolated self-hosted source check was
blocked before candidate checking because no admitted cached check worker was
available. Push then failed with HTTPS username/credential refusal; stored
GitHub account `ormastes` is active but its token is invalid. No interactive
login, retry, remote branch, PR, approval, or shared-worktree rebase occurred.

### L3 `check` startup capped follow-up

The exact Rust-seed route is `app.cli.check_entry` → `app.check.main`, with
214 Simple source files opened in the retained baseline trace. New immutable
baseline/candidate protocol manifests bind the absolute argv, controlled
HOME/XDG/TMP environment, seed/fixture/source/measurement-owner hashes,
30-second outer watchdog, 1 GiB target virtual-memory ceiling and identical
seven-cold/seven-warm cyclic schedules. Full receipts are in
`build/l3_check_startup_20260909/` and the metrics report above.

Cycle 1 changed modules outside the measured import route; cycle 2 failed to
remove the proposed broad runtime owner because other parser/discovery imports
retained it. Both are recorded `NO-REPRO`, and their source was reverted. The
final candidate removed collection-time `file_exists`/`find_spl_files` work in
favor of the existing expansion owner. Its source check and focused spec passed
(1/1), and the retained fixture had identical output with p50 changes of
-0.41% cold and -1.95% warm. Cold maximum RSS increased 516 KiB; this is modest
descriptive evidence only.

Astra final status: **FAIL — not approval-ready**. Baseline directory behavior
was shallow when a directory contained a top-level `.spl`; the candidate made
that path recursive. A mixed-depth tree therefore changed checked membership,
counts, diagnostics and possibly exit status, which the shallow fixture missed.
At the three-cycle cap no repair or rerun was allowed. The candidate source and
spec were removed without a semantic rerun; restored `app.check.main` SHA-256
is `263612b0ca7ab835ee8a5de49968e71ba50c18dce93d9fa461b1cba2c6fdbd11`
with no remaining diff. Raw manifests/report evidence is preserved. No commit,
push, authentication, broad check, self-hosted or Stage3/Stage4 claim.

## L5 provider-generation pin isolation — 2026-09-09

`ProviderGenerationPinV2` previously omitted its issuing manager identity even
though each manager restarts `pin_id`, provider handle and generation at one.
Two managers created with identical evidence could therefore accept and release
each other's locally identical pin. The focused RED run reproduced the defect:
6/7 examples passed and the foreign release consumed the receiver's pin, so its
later release failed with `PinUnknown`.

The isolated pure-Simple V2 owner fix adds the internally minted manager
identity to the pin and fixed-width little-endian cache-authority digest, and
rejects a foreign identity before pin lookup or release. The negative constructs
two managers with identical evidence and local coordinates, proves cross-manager
live/release rejection, proves both original pins remain live through authority
acquisition, and proves distinct authority digests. The owner source check
passed and the focused spec passed 7/7 in 447 ms. Frozen SHA-256 values are
source `1e94c544b84afdac2615b014d535000c553317a30a6b638f2b29834bda7c9fce`
and spec `fbec5d5ad5c54515332afdf6a58812a564200f15f1756a0286b184cbc7e28787`.

Astra status: **WARN — approval-ready for the narrow pin-owner isolation fix**.
Validation closes live/release/cache-authority cross-manager pin use, and the
single in-tree constructor is owner-controlled. Manager identity minting and
mutable manager operations remain externally serialized; there is no native or
concurrent-runtime qualification. Public mutable records are trusted bearer
coordinates rather than hostile same-process anti-forgery capabilities.
Activation and exact-retirement APIs remain unchanged manager-scoped coordinate
APIs, so this is not broad provider-operation authentication. The digest grows
from 432 to 440 bytes and intentionally invalidates prior opaque projections.
No loader/native ABI/L6 edits, integration wiring, commit, push, or production
availability claim were made.

## Schedule

## L10 fair feature-core correction — 2026-09-09

The staged C/Rust/Go fixtures previously performed 2,048 full passes per
process (1,024 warmup plus 1,024 timed) while Simple/Python/Bun performed 1,025
(one warmup plus 1,024 timed). An attempted correction gave all six fixtures an
apparently uniform one-pass source shape and removed C's peer-unique per-pass
validation. Existing separate runtime, startup, and compile schedule/measurement
contracts passed once, but they did not close execution parity.

The parity contract reached its third execution, but Astra rejected the
candidate: Simple and peer `warm_ms` units differ, Simple count is constant,
pure repeated calls remain hoistable, and no admitted Simple execution bites
the source-only contract. Status is **FAIL at cap; no candidate remains**. The
four fixture edits were restored to their pre-lane hashes without a fourth test.
Existing raw samples remain historical and were not modified or relabeled.
Rejected evidence and remaining redesign requirements are in
`doc/09_report/cross_language_l10_fair_fixture_correction_2026-09-09.md`.

## L10 Go/Bun comparator availability recheck — 2026-09-09

A cleared-environment, explicit-PATH host probe again found no callable Go or
Bun executable. All canonical system/per-user candidate paths were absent,
`whereis -b` found neither binary, and the host package database reported both
unavailable. Therefore the matched 15-sample collector was not run, no timing
row was fabricated, and no download, installation, container, or system
mutation occurred.

The prior C/Rust/Python runtime/startup/compile evidence remains byte-identical
with 15 samples per lane and claim set. The exact availability receipt and
preserved report/collector/schedule/raw-manifest hashes are recorded in
`build/l10_go_bun_availability_20260909/availability_receipt.txt` (SHA-256
`d3c50c5421d5189c66327fb047b3674ef60cefdabd851ab703a84bcdb0e5c2b7`) and
`doc/09_report/cross_language_l10_host_availability_2026-09-09.md`. Status:
**Go unavailable; Bun unavailable; comparison unavailable**.

## L2 runtime/interpreter PersistentSet subset guard — 2026-09-09

One bounded pure-Simple cycle added an impossible-by-cardinality rejection to
`PersistentSet.is_subset` before its key snapshot. The isolated focused spec is
2/2 PASS, the pre-existing PersistentSet suite is 64/64 PASS, and the source
check passed with the bootstrap seed's known JIT relocation fallback disclosed.
The frozen 2,048-left/0-right/256-call probe passed on both sides. It reduced
the internal one-sample bootstrap-seed interpreter time from 8,962,798 us to
5,641 us while structurally eliminating 524,288 materialized key entries; RSS
showed no improvement. Exact manifests, hashes, receipts, limitations, and the
invalid shared-user `RLIMIT_NPROC` attempt are in
`doc/09_report/l2_persistent_set_subset_guard_2026-09-09.md` and
`build/l2_runtime_perf_20260909/`.

Status is **focused PASS, unapproved**. The timing is provisional one-sample
bootstrap-seed evidence only. Independent review and admitted self-hosted
qualification remain; there is no commit, push, or production percentage claim.

## L2 admitted Stage2 tiny native-build memory profile — 2026-09-09

One discarded warmup and seven accepted unit-cache-cold/OS-warm tiny
native-build rows were collected from the exact compiler-only admitted Stage2
artifact under the Astra-approved frozen manifest and a 1 GiB/zero-swap cgroup.
All seven outputs passed the no-fallback, compile-completion, digest, and
execution oracle. Median elapsed was 6.36 s (range 5.21–6.76), median GNU
`ru_maxrss` was 192044 KiB, and median cgroup `MemoryPeak` was 156672000 B
(range 156491776–157827072). These are separate measures and no aggregate-RSS
or general improvement claim is made.

The one separate non-comparable `strace` attribution run completed successfully
with 14432 `openat` calls, 10117 failures, but only two unique `.spl` source
paths. Frozen source inspection identifies a cache-hit repeated-work bug:
`runtime_compiler.spl::_runtime_object_cache_dir` starts a full
compiler-version/runtime-tree content-hash shell pipeline before existing
runtime objects can be reused. Legacy cache inventories remained byte-identical.

Status is **bounded profile complete; NO-CHANGE**. An mtime shortcut would be
incorrect, the owner has concurrent changes, and the frozen Stage2 cannot
inherit a source edit. Next work requires an approved, generation-bound verified
runtime snapshot digest, exact invalidation/miss controls, and a newly admitted
candidate. Exact provenance, per-row receipts, trace hashes, limitations, and
acceptance gates are in
`doc/09_report/l2_admitted_stage2_tiny_native_build_memory_profile_2026-09-09.md`.

## L4 generated-binary memory/size lane — 2026-09-09

The exact admitted compiler-only Stage2 artifact (SHA-256 `319c7bd2...`,
152,703,072 bytes, unstripped with DWARF) received one bounded static section,
segment and symbol pass. PT_LOAD file bytes are 114,361,816; code is 58,093,904
bytes, rodata-family 41,878,432, unwind/exception 8,706,880, initialized data
5,523,240, and BSS/TBSS 3,477,828. Non-load file bytes include 34,825,933 bytes
of symbol/string tables and 3,408,796 bytes of DWARF. Exact provenance and raw
hashes are in `build/l4_generated_binary_size_20260909/`; the detailed report
is `doc/09_report/l4_generated_binary_size_2026-09-09.md`.

The admitted ELF contains both generated `compiler__...` symbols and hosted
Rust `simple_compiler::...` symbols. The defining `rt_native_build` archive
member has unresolved `NativeProjectBuilder` references, proving the path from
the bootstrap fallback to the monolithic Rust compiler and LLVM/Cranelift
closure. This lane is **NO-CHANGE**: removing/stubbing it would alter CLI
semantics and no admitted lazy provider exists. Next work must first admit a
typed/versioned lazy native-build provider/dynlib, baseline-safe loader,
explicit require/fail-closed fallback behavior, complete release receipts, and
continued Stage4 rejection of `native_all`. No size reduction is claimed.

## L6 aspect dynload quiescence capped handoff — 2026-09-09

The retained coarse `aspect_pack` pin cannot represent a callback that remains
live after its public facet pin is released. A cycle-1 focused reproducer
confirmed premature `UNLOADED` (`expected 2, got 1`). An isolated pure-Simple
owner/result candidate was then developed without changing `aspect_pack`, the
loader/provider, or any ABI. The final cycle uses a bounded module-global
canonical registry, internally minted monotonic lifecycle identities, copyable
handles/leases, generation binding, distinct callback/around/device leases,
and retirement only when every count is zero. Integration would require the
existing loader lifecycle gate to serialize creation and every transition;
the candidate makes no unsynchronized thread-safety or physical-unmap claim.

Final hashes are source
`a20ca4a39bde08c1b00d6ad7a09f0ecae55c8a3f51a931363ac560996f5a4e87`
and focused spec
`7839c0fe4cb8de38916423f3692e6b30e507d3620ce6a2d1dc66a5428f89f785`.
The source check passed. The final focused interpreter run executed 5 examples:
4 passed (nested quiescence, atomic around replacement, device-fence wait,
copied-handle canonical ownership) and 1 failed in 62 ms. The meaningful
duplicate-owner/copy/stale negative reached next-generation publication and
received `7` where incremented generation `8` is required. Astra classified
the expectation as correct and the observed result as a semantic/execution
defect whose exact runtime cause is not established from frozen source.

The three-cycle cap is exhausted. L6 is therefore **unapproved/escalated**;
there will be no fourth fix/retest cycle, loader wiring, availability claim,
commit, push, or unload activation from this candidate.

Bounded Astra source diagnosis now identifies an indexed-global write/read
coherence gap in the existing interpreter owner as a matching causal path;
the frozen executing binary is not yet bound to that source diagnosis. The
[L6 generation publication diagnosis](../../09_report/l6_aspect_generation_publication_diagnosis_2026-09-09.md)
freezes the minimal global-place correction, returned-versus-committed generation
probe, lease transfer checks, and separate loader/mapper activation gates.
Retain the candidate inactive; do not replace expected generation 8 with 7,
return a locally incremented value without proving canonical publication, or
treat logical retirement as permission to unmap. A new scoped authorization
is required before any reproducer or repair execution.

The original estimates (1–3 days for leaf fixes, 5–10 days for an admitted
profiled milestone, 2–4 weeks for integration, 3–6 weeks with broad target
qualification) are historical ranges, not remaining-time promises. Rebaseline
after L1 admission and L7 authority/codec scope freeze. Track dependency-ready
bounded tasks and blockers rather than repeatedly moving calendar promises.
SIMD/GPU and target-matrix qualification remain later independent work, not
blockers for correctness-first cache progress.

## L1 Stage3 corrective gate — terminal 2026-09-09

The independently reviewed HirLowering registry-authority repair received one
and only one guarded Stage3 attempt from admitted Stage2 SHA-256
`319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
It failed in HIR at 28/784 after 3:59.77, with 771,904 KiB maximum RSS and zero
swaps under a 4 GiB cgroup and `MemorySwapMax=0`. The first diagnostic is still
`src/compiler/driver/driver.spl: missing importing module surface`; 12,300
further phase-3 errors followed. The frozen source and Git snapshots were
stable, no candidate was emitted, and no retry or promotion is permitted.

L1 remains blocked. Before a new build authorization, diagnose why the
registry-owned helper still returns absence for the second HIR module despite
the reviewed call-site repair. Do not widen lifecycle APIs, rebuild, or treat
the absent candidate as qualification evidence. Evidence root:
`/tmp/simple-stage2-name-owner-fFW66D/repo/build/mini_builds/l1_hir_surface_stage3_cycle1_20260909/`;
log SHA-256
`5e91c2f4ffa150c9338dd44cd1a02adb11de09499d2b2b4373861c5418a65ab0`;
terminal receipt SHA-256
`33875a32cf85c90359125f3dff029ed83a48b8c99cd7f1762197a950cc4fb1b5`.

## Authoritative status reconciliation — 2026-09-09

This section supersedes only stale status/percentage statements for the scopes
named below. It does not erase their historical receipts or alter any other
lane. Percentages are bounded planning estimates: **artifact** is completion of
the presently scoped source/spec/report slice, while **activation** is admitted
integration or performance evidence. Neither percentage is a release claim.

| Scope | Artifact | Activation | Current authority |
|---|---:|---:|---|
| Runtime eight-symbol closure | 75% | 0% | Current source/retained-object evidence exists; no newly admitted runtime |
| Portable embedded body A | 0% | 0% | Candidate withdrawn after FAIL/cycle cap |
| Portable embedded body B | 30% | 0% | Frozen static candidate; Astra FAIL/cycle cap |
| L8 CAS/GC/database prerequisites | 55% | 0% | Useful frozen pieces, but owner/API, decoder and authority blockers remain |
| L9 persistent LSP planner | 40% | 0% | Corrected planner/spec/manual static PASS; deliberately inactive |
| L10 comparable profiling | 45% | 0% | Contract plus fail-fast SSpec package static PASS; execution remains NO-GO |
| Runtime compile-mode input policy | 65% | 0% | Frozen Astra FAIL with four defects; no fourth correction cycle |

The physical-summary fast path remains exactly three warm payload reads:
`.spl`, the prior `.tld`, and `__init__.tld`; a cold new file has only `.spl`
and `__init__.tld`. `.rr` remains coordinator scheduling input only: it may
select affected owners but is excluded from ordinary payload reads and cannot
inject or own macro bytes. `PortableBase`, `PortableOptimized`, `.sio`, all
existing objects/features and cache invalidation rules remain unchanged. All
storage work must reuse the existing CAS/journal/GC, Simple DB/PureDatabase and
server; no parallel database, CAS, writer or server is authorized.

### Runtime symbols: current source versus historical admission

The admitted Stage2 snapshot remains SHA-256
`319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
Its historical narrow native-build attempt failed to link exactly
`rt_file_fsync`, `rt_file_lock`, `rt_file_mmap_read_bytes`, `rt_file_unlock`,
`rt_madvise`, `rt_mmap`, `rt_msync`, and `rt_munmap`; that immutable admission
fact is not rewritten by later worktree changes.

Current source now places all eight public definitions in the shared hosted-C
owner `src/runtime/runtime_host_file_exports.c` (SHA-256
`6cfa0a4cff25ad097cb3ddeac5c9cfc93a5bf0881bc32937d345959a17d3329b`),
textually selected only by `runtime_native.c`. Retained implementation evidence
is `runtime_host_file_exports_implementation_2026-09-09.md` (SHA-256
`9b0e4202a319b6ca7602cfc020e6ea0824a1b799d25a212e1f62a0166e6ef6bf`);
the independent review (SHA-256
`b64eaf2809fafeb31295227db1d8ebddfd745ecee41bbefc4718e0e8655a193b`)
accepted the principal one-owner/ABI construction but rejected qualification.
Remaining gates are a corrected and independently accepted compile-mode input
policy; admitted Linux/macOS/Windows and supported-sysroot composition proofs;
exact one-provider archive/member receipts; mmap/msync/lock/error/nullability
behavior; and a newly admitted compiler/runtime. Rust-seed or retained-object
evidence cannot promote the historical Stage2 or activate a provider.

The follow-on compile-mode policy is also frozen, not accepted. Astra's
non-persisted review receipt records four exact defects:

1. The AArch64 sysroot expands unquoted `$CC` for libc/assembly before policy
   validation, so an injected `CLANG` command prefix can execute first.
2. Function-like protected definitions such as
   `-DSIMPLE_RUNTIME_HOST_FILE_EXPORTS_OWNER_V2(x)=1` evade classification.
3. Option operands are not tracked; for example
   `-o -DSIMPLE_RUNTIME_FREESTANDING_V2=1 -c source.c` counts an output name as
   a macro selection.
4. Response-file refusal misses embedded forms such as
   `-Wl,--start-group,@link.rsp`.

The same receipt also rejects the missing bypass scenarios, insufficient
textual ordering assertion, newline-only argument recorder, and completeness
claims in `runtime_compile_mode_input_contract_v1.md`. The lane exhausted its
three cycles: no fourth correction, cross-build, archive admission, provider
edit or activation is permitted under this plan revision.

### Portable embedded body A and B

Slice A is withdrawn/unimplemented after its independent FAIL and cycle cap.
Its frozen review blockers were the removed required `flat_pool_unescape`
import, reservations that did not bound actual allocation, incomplete work
accounting with a quadratic escape path, unspecified/unenforced canonical map
order, and incomplete evidence. Its generator-native route was also blocked by
the historical Stage2 eight-symbol failure above. Current worktree symbol
presence is not an admitted retry receipt.

Slice B remains a frozen inactive candidate with independent FAIL in
`portable_embedded_body_slice_b_astra_review_2026-09-09.md`. Its eight blocker
groups remain `B-SYMBOL`, `B-FIELDS`, `B-BOUNDARY`, `B-OWNER`, `B-GRAPH`,
`B-FACTS`, `B-BUDGET`, and `B-EVIDENCE`; 9/9 Rust-seed results are explicitly
non-qualifying. Both slices keep worker/publication paths closed. Resumption
requires a fresh bounded authorization after A's admitted generator/runtime
prerequisite and B's complete symbols/fields/boundaries, owner-issued graph
authority, facts/budgets, non-seed execution, manuals and independent review.

### L8 owner/API prerequisites

L8 retains the independently evidenced bounded-envelope-preflight and strict
UTF-8 requirements: reject size/kind/schema before payload slicing, hashing or
text construction, and use an accepted strict raw-byte validator with native
malformed/valid multibyte coverage. The currently dirty
`canonical_cache_codec_v1.spl` and `snapshot_contract_v1.spl` remain another
owner's work until an explicit freeze/handoff; this plan grants no overlapping
edit or acceptance.

A separate provider API mismatch must also close first. Clean
`src/os/smf/provider_loader.spl` currently lacks
`PROVIDER_ADMISSION_DIGEST_UNSTABLE`, `ProviderAdmissionOutcomeV1`,
`provider_admission_outcome_v1`, and `provider_query_abi_validate_v1`, while
clean `test/01_unit/os/smf/provider_loader_spec.spl` calls
`provider_session_query_v1` with an ABI digest even though the source accepts
only session plus request. Reconcile that API/spec under its owner and obtain
dirty-owner clearance before L8 consumes it. Only then may an exact-generation
admission-hit key bind canonical path + digest + kind + host target + interface
ABI/version + capability grant/requirement + trust manifest + immutable
generation. Remaining L8 gates are owner-issued durable/pin/root authority,
complete transitive typed closure, atomic all-root barrier/epoch handling,
crash replay before PureDatabase projection, strict decoder admission,
cross-process recovery/concurrency and independent review. Defaults and
availability remain false.

### L9 static PASS, inactive

The corrected `LspQuerySessionV1` planner (SHA-256
`22ad4dab182089cc418ebd11251864729c99ec3f87560463daaaaae8e34fc0bc`),
focused spec (`1a69d0118897a68bdca9a0faf2501f54616a35250efc37ca146c974613b81b2c`)
and manual (`d307d6d25c78df380c3921b0b09cf52254172350bc76343016452db0877937d8`)
have a bounded static PASS. They require one matching successful completion
before the next ready request, forward exact generation, keep
`answer_cache=false`, reject oversized workspace/request/generation identities,
retain the original absolute deadline across failure/reap, reject fallback
budget inflation, and allow only reap-before-once-only fallback.

This is pure inactive planning logic: no IO, worker hookup, existing-object
replacement or feature activation occurred. Remaining gates are admitted
Simple compile/spec/docgen; framed transport and provider integration;
crash/EOF/stderr/cancellation/reap behavior; exact invalidation against L7
semantic completeness; compiler/lib/MCP/LSP smokes; and measured warm startup,
representative latency and peak RSS on realistic fixtures.

### L10 static PASS, execution NO-GO

The frozen comparable-workload contract is
`cross_language_l10_comparable_sspec_contract_2026-09-09.md` (SHA-256
`06e2e6cb72877477ea6b4e12886617f18db3f7e23c8287027747b1360a1239b3`).
Its schema/setup/checker/spec/manual package received a scoped independent Sol
static PASS: exact closed schema/bounds, 21 scenarios in seven requirement
groups, six setup and ten checker/collector helpers, all 17 unavailable helpers
fail with `L10_PENDING`, and the manual matches. Astra review remains pending.
The schema module is not yet proven in the executable spec closure.

Execution remains **NO-GO**: Go and Bun are absent; no qualified Stage3/Stage4
Simple exists; historical C/Rust/Python rows are diagnostically useful but not
equivalent comparison evidence. Remaining gates are independent Astra review;
admitted Simple compile/spec/docgen; schema-closure integration; install-free
availability of each peer; identical input/output/checksum/features; bounded
warmup and at least 15 retained samples; p50/p95/CPU/RSS/binary identity; and
fail-closed collector validation. Until then there are no cross-language speed,
memory or binary-size claims and no substituted peer rows.

## L1–L11 continuity and next-agent reconciliation — 2026-09-09

<!-- codex-architecture: /root/three_file_compile_astra; parent-authorized plan-only edit -->

This additive reconciliation preserves the earlier receipts and their limits.
The historical **Ten lanes** table supplies L1–L10's exact titles; the later
**L11 optimize/SPipe knowledge handoff** supplies L11. Three-file compilation
is **L7**, not a replacement objective or a renumbering of the other lanes.
The following status incorporates later coordinator-supplied conversation
receipts and inspected current sources. Percentages are planning estimates,
not measured test coverage or proof of release readiness. Artifact and
qualification columns have different denominators; each “left” is the
complement of its own estimate. This reconciliation supersedes earlier lane
totals, but preserves narrower historical slice estimates and failed receipts.
No tests, builds, benchmarks, commits, pushes or activation were performed for
this plan update.

| Lane | Artifact done / left | Qualification done / left | Latest scoped result and remaining work |
|---|---|---|---|
| L1 — Self-host admission | 80% / 20% | 25% / 75% | Admitted compiler-only Stage2 retained. Later repaired-source bridge compiled 833 units, then failed candidate-bound sanity; no new admission or Stage3. Compiler owner must resolve that exact receiver/sanity boundary before dependent qualification. |
| L2 — Runtime hot paths | 88% / 12% | 35% / 65% | CMR/SDN and bounded work-count results retained. Runtime eight-symbol/compile-mode candidates remain unadmitted; production latency/RSS and matched runtime/generator closure evidence remain open. |
| L3 — Interpreter/compiler startup | 89% / 11% | 56% / 44% | Latest exact main/contract/manual correction has Astra static PASS (conversation receipt below). Integrated startup, invalidation and full-runtime smokes remain open; historical seed/Stage2 timings are diagnostic command classes. |
| L4 — Memory lifecycle | 88% / 12% | 30% / 70% | Mapping-lifetime accounting source/spec/manual have Astra static PASS. Positive-extent physical close failure/retry, actual unmap, admitted execution and RSS remain unproved. Existing mapper/provider owners must consume permits. |
| L5 — Generated-binary closure | 88% / 12% | 35% / 65% | MCP direct resource edge has independent Astra static PASS: two excluded units total 2,213 bytes; replacement/import growth leaves **2,197 net source bytes**. This does not qualify the older separate response-helper correction, recursive/native closure, startup or deployment. |
| L6 — Dynlib and aspect dynload | Unquantified / unquantified | Unquantified / unquantified | Frozen final-unpin interface and additive receipt-identity leaf have Astra contract PASS. Loader/mapper reservation, execution-quiescence, release and catalog integration remain open. The prior 82%/20% estimate has no current full-lane completion basis and is withdrawn; a leaf PASS cannot supply a new lane percentage. |
| L7 — Physical summary compilation | 75% / 25% | 0% / 100% | Physical-file broker source/spec/manual have Astra static PASS. Cold-two/warm-three bounded facade reads are authored; semantic-body authority, confined compiler execution, complete affected-query scheduling and atomic publication remain unavailable. Continue the existing A–F/G0–G8 owner DAG. |
| L8 — Pure-Simple database migration | 72% / 28% | 0% / 100% | Latest provider/TOCTOU/ABI correction is **frozen Astra FAIL**: the executor drops the cleanup session returned by dispatch. No fourth repair cycle or activation is inferred. Durable writer/CAS/codec, recovery and process-concurrency gates also remain open. |
| L9 — Persistent LSP queries | Active; current lane total not re-estimated | 0% / 100% | Retained planner/spec/manual static PASS; integration work active, `answer_cache=false`. Historical 40% refers only to the scoped planner. Transport/EOF/stderr/cancellation/reap, L7 semantic completeness, admitted smokes and performance evidence remain open. |
| L10 — Cross-language SPipe profiling | Active; current lane total not re-estimated | 0% / 100% | Collector/fixture work active. Historical 45% refers to the scoped contract package. Retained fair-fixture review is FAIL for timing normalization, executed-work proof, result-shape and incomplete-coverage claims; no matched full-language comparison is qualified. |
| L11 — optimize/SPipe knowledge handoff | 100% / 0% | N/A — documentation lane | Existing evidence-admission/failure-attribution skill additions and formatting/link receipts complete this documentation handoff. Root knowledge owner appends only newly evidenced lessons; no runtime or release-readiness claim. |

### Latest receipt identities and limits

The L3/L4/L6/L7/L8 verdicts below were supplied by the parent coordinator as
**conversation review receipts**, not invented persisted review reports. Hash
prefixes identify those exact reviewed snapshots; acceptance does not transfer
to later file contents. L3's unnamed main/contract/manual coordinates are
recorded exactly as supplied, without claiming that a guessed path was checked.

- L3: main `97c50dc...`, contract `bf0dc966...`, manual `6ebf7d06...`;
  final Astra PASS conversation receipt, scoped to the startup correction.
- L4: `src/compiler/99.loader/loader/mapping_lifetime_accounting_v1.spl`
  `49a40bc...`; focused spec `7e472c...`, mirrored manual `7f08af...`.
  All three current prefixes matched inspection. The manual explicitly excludes
  kernel mappings, native unmap and RSS claims.
- L5: `src/app/mcp/main_lazy_protocol.spl` `77cc578a...`, focused resource-read
  closure spec `4d36fe50...`, manual `95cadcef...`, and persisted
  [direct-edge report](../../09_report/l5_mcp_virtual_summary_resource_direct_edge_2026-09-09.md)
  `89dbcefe...`. Independent Astra review checked these identities and
  `1763 + 450 - 15 - 1 = 2197`. The source-only spec intentionally avoids
  process-global handler behavior; running it cannot itself qualify responses.
- L6: [final-unpin freeze](../../05_design/compiler/aspect_dynload/final_unpin_interface_freeze_2026-09-09.md)
  `d0b8749e...`; common `executable_mapping_receipt.spl` `974cedfd...`;
  identity spec `d6ac8ebc...`. Current prefixes matched. The newly present common
  leaf supersedes the freeze's earlier absence observation only for vocabulary;
  it does not issue leases/generations or implement physical release. Existing
  owners retain integration and the legacy authored-spec migration.
- L7: `src/compiler/80.driver/cache/worker/three_payload_physical_file_broker_v1.spl`
  `b2353111...`; integration spec `193253ad...`, manual `1b33b202...`.
  Current prefixes matched. Facade-read counts do not claim native syscall
  counts, actual worker execution or semantic/publication authority.
- L8: `src/os/smf/provider_loader.spl` `111b3e33...`,
  `src/app/simple_core/provider_dispatch.spl` `9376c344...`, TOCTOU spec
  `38e9f07e...` matched current inspection. ABI spec `fd863223...` is the
  coordinator-supplied reviewed identity. Current `executor.spl` projects
  dispatch into `SimpleCoreExecutionV1` without retaining
  `admission_cleanup_session`, corroborating the frozen final FAIL.

The retained [L1 bridge diagnosis](../../09_report/l1_stage3_executor_repair_diagnosis_2026-09-09.md)
records candidate-bound sanity failure after compilation, not a newly admitted
runtime. The retained [L10 independent fixture review](../../09_report/verify_l10_fair_fixture_correction_2026-09-09.md)
records the four comparison blockers; active subsequent work cannot erase that
receipt without an exact replacement review. L11's earlier knowledge-handoff
section remains the documentation completion evidence. No new numeric L6,
L9 or L10 umbrella estimate is inferred from a narrower source/manual PASS.

### Prior-session identity reconciliation and missing prerequisites

The current three files below match the complete SHA-256 identities in
`doc/09_report/verify_three_payload_semantic_binding_cycle3_2026-09-09.md`:

| Current owner | SHA-256 |
|---|---|
| `src/compiler/00.common/cache_contract/three_payload_compile_v2.spl` | `4cbcdb64799a8abcdeefa8a7a3c5a6dcf8d5267aba5ba72b5596f653dc433f23` |
| `src/compiler/10.frontend/cache_artifact/three_payload_semantic_closure.spl` | `8c9be64ba18f115b4cabcbe0dabd70bd68b890d00527b4652f692daf617e5b45` |
| `src/compiler/80.driver/cache/closure/three_payload_closure_packer_v2.spl` | `612c10a3edc1e1c14bee1ae699f6fa2834e2b64780adbf2ac47a7bc987ac040a` |

The six earlier binding defects must not be reopened as missing implementation:
checked reads, authority refusal, aggregate preflight, call-contract identity,
multi-producer ordering and current negative cases/manuals received the later
inactive static PASS. That PASS does not qualify execution, body authority or
the entire PR-A–E rollout. Physical raw-body framing/corruption/ownership
corrections in the integrated report are also retained accomplishments.

Slice A's bounded decoder remains withdrawn: inspected `20.hir/hir_codec.spl`
has the legacy codec and no bounded `HirDecodeLimits` entrypoint. Resume from
`portable_embedded_body_slice_a_runtime_closure_contract_2026-09-09.md` and
the A review's import, real allocation/work ledger, canonical ordering and
evidence requirements; do not report the abandoned decoder as available.

Slice B has changed since its historical independent FAIL. The current
`portable_object_profile_v1.spl` hash is
`77c6cb5f506d5646116ae75739d854aa783d02c78f2db44a7e53389e61befce5`,
not the reviewed `68f8b760...`; `portable_body_semantics`, `portable_body_graph`,
`portable_body_budget` and `portable_body_profile_types` now exist. These are
unqualified current candidates, not an inherited PASS or an exact-byte repeat
of the old FAIL. Use B-SYMBOL/FIELDS/BOUNDARY/OWNER/GRAPH/FACTS/BUDGET/EVIDENCE
as a delta-review checklist. Its bounded-byte signature still depends on missing
Slice A, and both semantic-byte admission and completeness issuance are false.

Slice C's existing `gateway/semantic_scope_authority_v1.spl` performs structural
preflight but has no live writer/public-summary/attempt/semantic-contribution
port; availability remains false. The existing worker now performs bounded,
path-free **in-memory object** reads through SOSIX/SimpleRing. This is additional
logical broker evidence, not physical-file or confined compiler execution.
`three_payload_worker_confinement_available_v1`, affected-domain authority and
generation publication remain false. No new service or duplicate receipt store
is needed to complete these existing owners.

### L7 semantics, read accounting and implementation DAG

The warm frontend worker consumes exactly the source `.spl`, prior `.tld`, and
one sealed effective `__init__.tld`; a new file consumes only source and init.
Prior `.tld` is optional history, never a synthetic prerequisite to its own
creation. The initializer includes transitive effective scope, not merely the
current directory. `_tldr.spl` and `tld show` are renderings of canonical summary
records, never another imported source or semantic authority.

Macro/CTFE execution requires verified tokens/hygiene/captures, invocation inputs
and the complete executable helper closure. Generic instantiation, trait-default
use, inlining and body-observing/around aspects similarly require their consumed
bodies. These can fit the three-input contract when their original canonical
bytes and verifier-owned identities are embedded as indexed sections inside
the two admitted TLD containers. Current pure-closed-function profile work does
not implement all of these semantic families; each existing owner must supply
its complete supported profile before that family is eligible.

Concrete trait, extension and call-only aspect calls can remain symbolic when
signature, effects, coherence/selection/order and positive/negative candidate
witnesses suffice. Ordinary advice-body changes do not change the consumed call
contract; object provenance stays separate. Dynamic aspects keep existing leases,
generation checks and dispatch semantics. Body observation changes eligibility.

A digest reference to a separately stored shard does not include that shard's
bytes: opening it is another physical input. Lazy section decoding within an
already acquired TLD preserves the input set; external lazy CAS reads do not.
Track distinct physical payloads, actual open/read calls, bytes, decoded/retained
bytes and preparation/control-plane reads separately. Three payloads alone do
not prove three syscalls or bounded memory. Missing bodies, unsupported macro IO,
incomplete witnesses or size limits require typed refusal/explicit multi-input
fallback outside this profile. Target lowering/linking/runtime separately need
selected object/library/device bytes unless already embedded/retained; those
reads cannot be claimed absent from whole-build/startup measurements.

`.rr` remains coordinator-only scheduling/rebuild projection, never a normal
forward-worker input or macro-content owner. Changed/new/deleted candidates
require old/new membership and absence domains even when no old reverse edge
exists. Successful reevaluation replaces outgoing reads and RR deltas atomically
with summary/object roots; failure retains the old admitted generation.

1. **Runtime + A (L1/L2):** recover exact failed generator identities, qualify
   runtime closure, then bounded existing codec/generator and shared ledger.
   Preserve trusted wire compatibility and freeze deterministic regeneration.
2. **B and C, independent scopes:** B derives complete typed body/symbol/effect
   facts with indexed graph/work bounds; C binds existing writer/pin/generation/
   attempt and semantic-owner authority, serialized with L8. Typed fixtures may
   advance before A, but untrusted-byte acceptance cannot.
3. **D after A+B:** existing CAS kind/store and summary adapters bind exact raw
   bytes, typed object digest, profile, module and section; public DTO hashes
   cannot mint grants. No new IR, store, decoder grammar or server.
4. **E after C+D:** existing frontend/packer/RR owners derive complete closure
   and forward reads, preserve call-contract cutoff, and schedule authenticated
   old/new domains/SCCs. Physical broker fixtures may be developed independently;
   production confined compilation waits for these admitted inputs.
5. **G5/G6 then G7:** prove real cold-two/warm-three source-driven compilation,
   deny fourth-input/RR/ambient/FFI escapes, and verify supported Base/Composed
   portable outputs through existing HIR/SMF owners. Publish through existing
   writer/CAS/journal/GC after immutable blobs and before rebuildable DB lookup;
   test epoch/cancellation, pins, crash/replay and all-root atomicity.
6. **F/G8 and L10:** independent semantic/manual/runtime review; clean versus
   cached outputs/diagnostics including macros, generics, traits, extensions,
   static/dynamic aspects; corruption/bounds/negative-witness cases and required
   compiler/lib/MCP/LSP smokes. Measure matched compiler/interpreter/generated
   binary timing, CPU, RSS and deduplicated deployment bytes only when admitted.

L7's direct prerequisites are L1/L2 runtime qualification, L4 lifetime/pins,
and L8 durable cache authority. L3 resolution and L5 generated closure are
integration/performance peers, not reasons to discard existing functionality.
L6 supplies dynamic/portable loader compatibility and consumes L7 portable
results. L9 consumes L7 completeness for semantic cache reuse. L10 verifies
the claimed comparisons, and L11 records supported lessons from all lanes.

At this handoff the four live team handles are root, `pure_simple_next`,
`three_file_compile_astra`, and `three_file_compile_impl`. Root owns scheduling;
this Astra lane owns only this additive plan update; the implementation lane
is auditing an isolated physical-broker slice; the migration lane retains its
existing scope. These observed handles are not durable ownership locks. Recheck
live sessions and explicit dirty-file handoffs before refilling slots. Shared
codec/writer/source owners remain serialized; a plan assignment does not start
a process or supply a verification receipt. Prior capped attempts stay closed
unless a newly scoped continuation is explicitly assigned by the coordinator.

### Reconciliation delta after `ce3f51c9` — 2026-09-09

This subsection appends the coordinator-supplied outcomes received after plan
SHA-256 `ce3f51c9a4b97ca38b31310703c5163d7ec0263276538bebfaefab389fbddc97`.
It does not replace the earlier evidence ledger, lane estimates, dependency DAG
or receipt limits. “PASS” below is scoped to the named static/artifact review;
it is not activation, admitted execution, deployment or release qualification.
No new umbrella percentage is inferred. The only new numeric slice estimate is
the explicitly supplied L9 bridge estimate.

| Lane | Latest static/artifact reconciliation | Activation/qualification boundary |
|---|---|---|
| L2 — Runtime hot paths | Documentation-only bug handoff PASS: [native-build core-C runtime archive rebuilt per invocation](../../08_tracking/bug/native_build_core_c_runtime_archive_rebuilt_per_invocation_2026-09-09.md), SHA-256 `d3f927bc70c80425efa21d2a3f6cc9ed039403212e316c0ce76b0309b51ff790`. It binds the admitted owner proof and records that Rust `NativeProjectBuilder` selects a fresh per-invocation TempDir, so archive reuse cannot hit. | No runtime fix or activation. The dormant Pure-Simple route still requires explicit-entry/source routing admission and immutable C-input authority. The bug forbids a Rust application workaround or a new cache. |
| L3 — Interpreter/compiler startup | Prior final Astra static PASS is retained unchanged. | Integrated startup/invalidation, admitted runtime and performance qualification remain open. |
| L4 — Memory lifecycle | Prior mapping-lifetime accounting static PASS is retained unchanged. | Positive physical mapping/unmap/retry execution and RSS qualification remain open. |
| L5 — Generated-binary closure | Final Astra static PASS: inspected direct source-closure edge excludes `1,763 + 450` bytes, with `+15` replacement-owner growth and `+1` import spelling, for **2,197 net source bytes smaller**. | This is direct-edge source accounting only, not recursive compiled/native bytes, startup, deployment or the separate older response-helper qualification. |
| L6 — Dynlib and aspect dynload | Receipt vocabulary and stale authored-spec correction have scoped static PASS. | Loader/mapper consumption, generation/lease integration, quiescence, physical release, catalog wiring and activation remain open. Vocabulary/spec PASS does not issue a live receipt. |
| L7 — Physical summary compilation | The physical-file broker retains scoped static PASS. The additive live-port value contract has final static PASS at source `3c70b2bb0a721dbf6ad3e0ccfe5ca913a5493d9963a747134c62a5bac9943a97`, spec `e2dc88aeb0706216dbad17e770016cb323e3ffdda35735dc9b1be67fa3e0178c`, and manual `192e83b29f5cfde99ac49e1bcbfebadb630e6be5d3546925f3776a1752dee1d7`. It preserves nine-field coherence, five ordered contribution requests, source/prior/init read limits and coordinator-only RR. | The live-port contract is deliberately inactive: availability remains false and writer, public-summary, prepared-attempt and semantic-contribution owner ports are absent. No compiler execution, publication or activation is qualified. |
| L8 — Pure-Simple database migration | Frozen final Astra FAIL is retained: the executor projection drops the cleanup session returned by provider dispatch. | No fourth correction cycle or activation. Provider lifetime, cleanup ownership and the remaining durable cache/database gates stay open. |
| L9 — Persistent LSP queries | Final bridge static PASS: source `03c9b02bdd631f8aba6fdee084567e328817d0f3643dba375cce1e5bed357f2e`, spec `10b3af1032880c26ed38fad2e636d2b0c01b349afe39b16cf46b687a3b408d33`, manual `b6600f5437fc228bb5d2312ecf5f0fa09d186308a32d0ff3d24d6cd5bf562092`. Scoped bridge artifact estimate: **45%**. It preserves exact request/generation forwarding, bounded encoding, owner-bound deadline/fallback validation and `answer_cache=false`. | Qualification estimate: **0%**. No worker/process/server authority, persistent transport integration, activation, admitted smoke or latency/RSS evidence is supplied. |
| L10 — Cross-language SPipe profiling | Group 1 is frozen FAIL with four defects: timing normalization, executed-work proof, result-shape equivalence and incomplete-coverage claims. Thirteen checks remain explicitly pending. | No matched cross-language activation or performance qualification; pending markers and unavailable peers cannot be converted into substituted results. |

L3/L4 therefore remain prior scoped static PASS, L5/L6/L7/L9 add only the
named artifact receipts, and L8/L10 remain frozen FAIL. None of these deltas
authorizes a seed/native run, production activation, commit, push or release.

### L7/L10 dependency and capped-gate reconciliation — 2026-09-09

This additive handoff follows plan SHA-256
`474aa99e85b6b299051f925092aa58d01fde2b8215fdf05ca8241feabdf3d23e`.
The coordinator supplied the live statuses below; this documentation slice ran
no compiler, test, collector or benchmark. The historical receipts remain
immutable and keep their original scope. The detailed status and next acceptance
boundaries are retained in
[L7/L10 reconciliation report](../../09_report/global_perf_l7_l10_status_reconciliation_2026-09-09.md).

| Work item | Latest bounded status | Remaining acceptance boundary |
|---|---|---|
| L1 / Stage2 | Stage2 work is live under its existing owner. The previously admitted compiler-only subject remains historical evidence, not automatic admission of the live candidate. | Await the exact live terminal/admission receipt. No restart, competing rebuild, full-CLI qualification or Stage3/Stage4 success is inferred. |
| L7 contract | Source review GO; coverage and runtime qualification pending. | Real contribution/worker coverage, admitted execution and actual cold-two/warm-three reads remain required. Source GO does not prove physical restriction or semantic completeness. |
| L7 bounded HIR | Stopped after three invalid-oracle cycles. | Retain failures; first correct and independently review the oracle in a newly scoped lane. No fourth attempt or production claim from this lane. |
| L7 portable body | Body path remains inactive; root-entry result is diagnostic. | Qualify the production body owner, transitive semantic closure and actual worker execution; the root-entry diagnostic cannot substitute for that integration. |
| L7/L8 CAS prerequisite | Corrected test awaits review. | The reviewer must establish that the corrected test exercises the authoritative publication/recovery/root lifecycle. Test correction is not a CAS service PASS. |
| L10 statistics | Static PASS. | Execute qualified statistics/admission coverage over complete matched receipts; static formula/schema review supplies no timing or comparative result. |
| L10 adapters | Cycle-2 review pending; C/Rust/Python raw correctness outputs retained. | Independent review of parser/error/work/result equivalence and remaining language adapters; no performance admission from the raw diagnostic intervals. |
| L10 collector | Stopped after three NO-GO cycles. | A separately scoped continuation must address the recorded rejection causes before new execution. No fourth collector cycle, partial success average or substitute language result. |

Benchmark inventory confirms that current Class-A v3–v5 artifacts are
synthetic/selftest evidence, historical matrices contain missing or unequal-work
rows, the earlier L10 fair-fixture correction was reverted at its cap, and the
equivalent Rust/Go benchmark fixtures lack retained timing/RSS receipts. None
supports a historical ranking or a current Simple/C/Go parity claim.

The change from hours to days reflects newly discovered dependencies: the
initial estimate covered local source/contract edits, while completion also
requires oracle validity, compiler admission, production body/worker wiring,
durable CAS authority, adapter equivalence, complete collector receipts and
independent review. Several dependencies now have capped failures or pending
review. These are distinct deliverables on the dependency path, not repeated
green checks. Earlier hour/day estimates are planning context only; this update
sets no replacement ETA, completion percentage or performance prediction.

### Terminal Stage2 cycle-3 handoff — 2026-09-09

This update supersedes the earlier **Stage2 live** status. The coordinator's
cycle-3 attempt ended in a real link failure: `GenericTemplate.is_err`,
`CompilerDriver.compile_to_vhdl`, and `MirBuilder.emit_comment` are unresolved.
No next-stage candidate/admission follows. The current three-cycle budget is
exhausted: **no fourth build or relink in this session**. Preserve the recovery
tree, cache, objects and log. Exact hashes, proposed repairs and acceptance are
in the [terminal reconciliation](../../09_report/global_perf_l7_l10_status_reconciliation_2026-09-09.md#terminal-stage2-cycle-3-and-next-session-handoff).

The next session must combine typed template-load Result alignment, the
approved VHDL registration import and fatal GPU-CAS diagnostics before one
newly scoped cache-preserving admission continuation. These are proposed
repairs, not a passed build. Changed units must invalidate through the existing
cache owner; no rebuild per individual undefined symbol.

DynSMF has coordinator-reported scoped **source PASS / runtime pending** at
lifecycle `bb5f67325985ff60f40232ce53f73b36220fa205a8b8bc4b42bf9a18d8b7e040`
and session `1ea555132181d2e491ff9e6666c705c69c537dfc642f133dd27cfa41c52a7699`.
This provides no mapped-payload or lifecycle/performance qualification. L7
bounded-HIR and L10 collector remain stopped at their caps. The isolated SPipe
cooperative-TDD source lane ended cycle 3 **FAIL** with no admitted runner
attempt. L7 coverage/runtime, inactive body, CAS corrected-test review and L10
adapter review retain their pending boundaries. No umbrella PASS, ETA or
speedup is inferred.

### Applied isolated link-fix freeze — 2026-09-09

The three repairs above are now **applied and source-reviewed PASS** in
`/tmp/simple-stage2-recovery.FtQUKS/`; the earlier proposed-only description is
historical. The coordinator supplied VHDL and Generic review verdicts; the GPU
transfer also received this reviewer's direct source PASS. Exact independently
hashed isolated owners:

| Owner under `src/compiler/` | SHA-256 |
|---|---|
| `80.driver/driver_aot_output.spl` — VHDL registration | `9bde1c731e5ab0c167d09915a4cd55551fce70294ab419e808fa357db3b5d94c` |
| `00.common/compilation_context.spl` — typed load contract | `0603e7eb7191a543381d106a0e1ec2afafb85ae47485e5551222ed3a14141ebb` |
| `80.driver/pipeline/compiler_context.spl` — compiler provider | `1a2347a95ccdfaaf020254497a2a4d3cb37117d911ed75d709248bd5e0db0b9f` |
| `70.backend/linker/linker_context.spl` — linker provider | `e151283a1354e299a09257ac8d4a714a3e2eea59b5581159fdfd722a8538b256` |
| `40.mono/instantiation.spl` — Result consumer | `a7dc8182a108508e9fec9e0ab540278aa5580f8486793bfd69687c8f99f576bb` |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl` — GPU repair | `bb7b91ef3bf78f84e57c8b247d8b2c72eac2c8bc33c474c500e2db3d8838fc32` |

**No fourth build in the current session.** Source PASS is not behavioral,
link or admission PASS. The next fresh session uses one combined canonical
build with the preserved cache/objects and normal changed-unit invalidation.
Require all three unresolved-symbol failures to be absent and actual link
success, then the existing Stage2 sanity/receiver/admission gates. Preserve
failed objects as evidence; do not claim they were relinked successfully. Full
behavioral, GPU/VHDL capability and subsequent stage qualification remain open.

## Related plans

- `doc/03_plan/agent_tasks/compiler_semantic_cache_manager.md`
- `doc/03_plan/agent_tasks/compiler_loader_script_crosslang_perf.md`
- `doc/03_plan/agent_tasks/environment_optimized_dynamic_libraries.md`
- `doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md`
- `doc/03_plan/agent_tasks/simple_compiler_performance_memory_efficiency.md`

## Wave 2026-09-12 — interpreter perf, gate-sync and L9 lane (Claude session): features this wave completes

<!-- claude-lane: wave declaration; status per row is the row's own evidence, no percentage or delivery date -->

Root scheduling note: this wave runs beside the three live Codex sessions in
`/home/yoon/dev/simple` (branch `codex/spipe-local-knowledge-setup`, dirty
tree) and does not touch their owned files (UTF-16 direct sink,
`core_string.spl` cursor, `expand_check_targets` index, `simple_lsp_mcp`
virtual-source registry, L7 issuer/RR worker, L8 namespace/GC, L6 mapper,
L10 process observation). Every item below has a red-first spec, binary
identity on every timing, and lands through its own `work/*` PR.

Integration note (2026-09-12): the eight PRs listed below (#544, #545, #548, #549,
#550, #552, #553, #557) are no longer landed individually. Their FEATURE
commits — without the per-branch `chore(check): unblock the two push gates`
commit, which gate-sync supersedes — are cherry-picked in that order onto
`work/interp-perf-wave-2026-09-12`, which starts at the gate-sync commit
`2d082ac144e` (PR #561). One branch, one PR, one verification pass; the
original commit messages and their evidence are carried verbatim, with
`-x` provenance lines back to each source sha.

| Item | Lane | Vehicle | State (2026-09-12) | Evidence |
|---|---|---|---|---|
| Plan L3 query leaf-import slice (approved 2026-09-09, never pushed) + L2 `PersistentSet.is_subset` cardinality guard | L2/L3 | wave PR (this branch) | PR open, required check queued | `test/02_integration/app/query_log_modes_spec.spl` 7/1→7/0; `test/05_perf/runtime/persistent_set_subset_spec.spl` 9152 ms→<200 ms |
| Seed interpreter: `substr` / `char_at` / `s[i]` no longer rescan the whole string per call | L2 | wave PR (this branch) | PR open | ratios 14.58/8.44/8.36 → 3.99/4.00/4.00 at 4× n; `string_char_index_scaling_spec.spl` |
| `utf16_to_utf8` fused single pass (record corrected: linear, not quadratic) | L2 | wave PR (this branch) | PR open | 1,039,755 → 301,556 µs on the record's input; `utf16_to_utf8_direct_conversion_perf_spec.spl` |
| L9 G1 in-process LSP query adapters + G2 bounded cross-file search (full `src/**/*.spl` coverage, 0 child starts); planner `LspQuerySessionV1` landed verbatim | L9 | wave PR (this branch) | PR open; **G3/G4 blocked** on `rt_process_owned_v4_*` streaming-stdin primitives (contract in the L9 blocker note) | definition 7,940 ms → 20.6 ms / 20 queries; `lsp_query_inproc_spec` 7/7, `lsp_bounded_search_spec` 16/16 |
| Seed interpreter: local dict `insert/set/remove/delete/merge` in place | L2 | wave PR (this branch) | PR open | 14.69/19.37/15.49/11.78 → 3.88/4.11/3.93/3.86; `dict_mutator_scaling_spec.spl` |
| Seed interpreter: array mutators on a local inside an expression (`acc + arr.pop()`) | L2 | wave PR (this branch) | PR open | 15.4/13.4/17.7 → 1.35/4.29/2.06; `identifier_mutator_in_expression_scaling_spec.spl` |
| **Structural**: one place-aware in-place mutation kernel for every nested-place receiver (`self.inner.xs.push`, `rows[i].push`, `self.d.insert`, `arr[i].m()`, 2-level index assignment) + the interpreter component scaling spec (one `it` per shape) | L2 | wave PR (this branch) | PR open | eight quadratic shapes (8.5–25.6×) → 3.9–4.0×; `interpreter_component_scaling_spec.spl` 15/23 → 23/23 |
| `for k, v in d.items()` destructures; `Dict.items` bound under JIT | L2 (correctness) | wave PR (this branch) | PR open; design conflict recorded (bare comma: seed enumerate vs pure-Simple destructure) | `dict_items_for_loop_spec.spl` 5/5 |
| Seed follows pure-Simple: bare comma in `for` = tuple destructure always; enumerate spelled `.enumerate()`; call-site census + migration | L1 (bootstrap parity) | branch `work/for-comma-destructure` | in progress (user decision (a) on 2026-09-12) | `test/04_smoke/compiler_unparenthesized_tuple_for*.spl` RED → GREEN target |
| Gate-sync: required CI job green on `main` again (hot-loop baseline +3/−1 with plan note, chrome shim parity row, two bootstrap-tier ledger rows identical to Codex's `codex/push-gate-ledger-fix-20260912`) | L0 | branch `work/gate-sync-2026-09-12` | pushing; lands FIRST, the eight PRs above rebase onto it | `required_ci_job_red_on_main_hotloop_and_parity_2026-09-12.md` |
| Guard wiring where missing (orphaned guards since 2026-08-15 wired or opted out with a reason; `push-no-direct-rt` manifest/hook agreement) — **K** | L0/L11 | PR **#579** | **LANDED** 2026-09-12 (merged `b9667d6584f`) | 116 orphaned guards wired advisory; `check-guard-wiring.shs` unwired baseline ratcheted **725 → 607** |
| Sanctioned bootstrap on current `main` (`bootstrap-from-scratch.sh`), pure-Simple fixes only, honest receipt — **M** | L1 | PR **#575** | **LANDED** 2026-09-12 | two pure-Simple defects that broke the Stage 2 link fixed; linker-deferred-method record filed |
| Todo-DB triage: close stale todos, sync statuses, reseal crc32 | L11 | PR **#576** | **LANDED** 2026-09-12 | `doc/08_tracking/todo/todo_db.sdn` resealed; bug-db half split out to #578 |
| Bug-record triage: bug shards + `bug_db.sdn` sync (the bug half of #576) | L11 | PR **#578** | **LANDED** 2026-09-12 | shard/`bug_db.sdn` disagreements reconciled |
| **L5 generated/deployed binary closure** — measurer + per-(entry, lane) ratchet (A), MCP entry (B), LSP-MCP entry (C), check/lint entries (D), seed cross-lane parsed-source cache (E), deployed-closure manifest + dedup gate (F), spec-runner startup closure (G) | L5 | branch `work/l5-integration-2026-09-12`, 9 commits | integrated, not pushed | per-entry both-lane table immediately below this table; `check-entry-closure-ratchet.shs --all` **PASS — 20 pairs, 0 grown**; `cargo check --release --bin simple` rc=0 |
| Plan leftovers with no owner (L9 G3/G4 runtime primitive, L4 bounded caches, L5 MCP/LSP closure delta, L11 traceability for this wave's specs) | L4/L5/L9/L11 | branch `work/plan-elg-leftovers` | triage then ≤3 items | `N_triage.md` then per-item records |
| EGL fan-out — Environment-optimized dynamic Libraries, packages 2/4/5/7 (packages 1/6/8 arrive merged in the core base `bd8df49e8d4`; L7/L8 stay with Codex `codex/gl-production-current-main-sol-20260912`) | EGL | ten agents N, P, Q, R, S, T, U, V, W, X, core agents (packages 2/4/5/7) work off the core base `bd8df49e8d4`, one `work/egl-<topic>` worktree each | **LANDING via PR from `work/egl-wave-2026-09-12`** (2026-09-12). The branch carries Codex's `codex/gpu-e4-e5-production-sol-20260912` (24 commits, packages 1/6/8) merged at `bd8df49e8d4`, the nine agent commits P/W/V/U/X/T/N/K plus the collected-receipts commit, the U2/X2/V2 follow-ups applied from their worktrees, and `origin/main` merged in (one conflict, `must_check_db.sdn`, resolved to main's regenerated side). Codex hit its usage limit, so its branch does not land on its own and this PR carries it. Gate work done on the branch rather than deferred: the +9 direct `rt_*` sites the base introduced are routed through `std.sffi.host` aliases (delta now 0, baseline untouched), two NEW unwired guards closed, one manifest row the merge silently dropped restored, and a false-positive in the merge-conservation extractor fixed with its selftest still 6/6. Agents Q and S did not land: Q is blocked on a 2-token parse defect in the parser-variant build plan, S is frozen. | `EGL_BRIEF.md`; `doc/03_plan/agent_tasks/environment_optimized_dynamic_libraries.md` package-status table rows 2/4/5/7/8 updated with what this branch delivers and what stays Codex-owned; `doc/03_plan/agent_tasks/environment_optimized_dynamic_libraries_receipts_2026-09-12.md` carries the per-agent receipt paragraphs |


### L5 entry-closure delta — all ten entries, both lanes (2026-09-12)

Re-measured by the integrator on the integrated branch with L5-A's
`scripts/perf/measure-entry-closure.shs`, `--samples 0 --verify-cold`, hermetic
`HOME`, `SIMPLE_EXECUTION_MODE`/`SIMPLE_TEST_MODE` cleared, binary
`/home/yoon/dev/simple-wave/src/compiler_rust/target/release/simple`
(51,308,600 B, sha256 `ef528c608113173c0c1aef6edb10ac17f9bf68886f34e05aff21a39c67515562`).
"Before" is `config/perf/entry_closure_baselines.sdn`, the wave baseline.
Only the PHYSICAL pair is ratcheted; `spl_opens` and `unit_spellings` move with
the seed's cross-lane read behaviour (L5-E), not with an entry's imports.

| entry | lane | files before | after | Δ files | bytes before | after | Δ bytes | owner |
|---|---|---:|---:|---:|---:|---:|---:|---|
| `cli-version` | default | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `cli-version` | interpreter | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `cli-help` | default | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `cli-help` | interpreter | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `mcp-help` | default | 131 | **47** | **−64.1%** | 1,323,864 | **404,093** | **−69.5%** | B |
| `mcp-help` | interpreter | 131 | **46** | **−64.9%** | 1,323,864 | **378,501** | **−71.4%** | B |
| `mcp-info-call` | default | 131 | **80** | **−38.9%** | 1,323,864 | **643,244** | **−51.4%** | B |
| `mcp-info-call` | interpreter | 131 | **80** | **−38.9%** | 1,323,864 | **643,244** | **−51.4%** | B |
| `lspmcp-help` | default | 38 | 38 | +0.0% | 325,005 | 326,336 | +0.4% | C — **miss**, see below |
| `lspmcp-help` | interpreter | 38 | **6** | **−84.2%** | 325,005 | **41,252** | **−87.3%** | C |
| `lspmcp-3frame` | default | 38 | 38 | +0.0% | 325,005 | 326,336 | +0.4% | C — **miss**, see below |
| `lspmcp-3frame` | interpreter | 38 | **6** | **−84.2%** | 325,005 | **41,252** | **−87.3%** | C |
| `query-help` | default | 125 | 125 | +0.0% | 1,262,376 | 1,262,376 | +0.0% | no L5 owner (L3 landed earlier) |
| `query-help` | interpreter | 107 | 107 | +0.0% | 1,140,426 | 1,140,426 | +0.0% | no L5 owner |
| `check-help` | default | 132 | **27** | **−79.5%** | 1,302,861 | **220,550** | **−83.1%** | D |
| `check-help` | interpreter | 114 | **27** | **−76.3%** | 1,180,911 | **220,550** | **−81.3%** | D |
| `lint-one-file` | default | 387 | 309 | −20.2% | 4,307,651 | 3,767,766 | −12.5% | D — **miss**, see below |
| `lint-one-file` | interpreter | 291 | 291 | +0.0% | 3,645,845 | 3,645,816 | −0.0% | D — **miss**, see below |
| `test-one-spec` | default | 352 | 270 | −23.3% | 3,004,187 | 2,734,137 | −9.0% | G — **miss**, see below |
| `test-one-spec` | interpreter | 352 | 270 | −23.3% | 3,004,187 | 2,734,137 | −9.0% | G — **miss**, see below |

**Honest misses, none of them averaged away.**

- **`lint-one-file` (D, both lanes, target −25%).** Two blockers, both outside
  the row and both filed. (1) `lint_entry.spl` was REVERTED: leaf-importing it
  makes the whole lint/fmt/fix program stop JIT-compiling —
  `[jit-fallback] unresolved external symbol 'io_runtime_cwd': whole module
  dropped to the interpreter` — because
  `src/lib/nogc_sync_mut/sffi/system.spl:8` aliases
  `use std.io_runtime.{cwd as io_runtime_cwd}` and only the `std.io` hub was
  co-compiling that symbol into the same JIT module; under
  `SIMPLE_JIT_STRICT=1`, `simple lint --help` then exits 1 with NO output.
  (2) Even with that swap the entry has a structural floor of 301 files /
  3,388,952 bytes: 8 of the 10 `compiler.tools.lint._LintMain.*` submodules
  each pull the full 290-file / 3,316,828-byte cluster on their own, so
  splitting the `compiler.tools.lint.main` facade buys nothing. The landed
  −20.2% is one dead hub import
  (`src/compiler/35.semantics/resource_families.spl:5`), nothing more.
- **`test-one-spec` (G, target −25%).** The integrator's re-measurement is
  270 / 2,734,137 in BOTH lanes — **−23.3% / −9.0%, short of the target on
  both axes.** L5-G reported 184 / 1,757,778 from a direct shell run; that
  number did NOT reproduce here from a direct shell run, and 270 is within one
  file of the 269 the ratchet independently measured and of the 269 G itself
  measured when the measurer ran nested under `bin/simple test`. The entry is
  bimodal on the shared session-daemon path (G measured 352 vs 332 pre-fix for
  the same lane), so 184 is currently an unreproduced best case and is not
  quoted as the result. The import work is real and landed: neither the 270-
  nor the 184-file run opens any of `io/{tcp,udp,buffer,event_loop}.spl`.
- **`lspmcp-*` default lane (C).** Does not move, by mechanism, not by
  omission: the front end whole-module-compiles every top-level function in
  `main.spl` before running any of them (the pristine tree already emits
  `[CODEGEN-STUB-FALLBACK] body compilation failed for
  'handle_resource_templates_list'` on a bare `--help`), so a function-local
  `use` — which changes name scoping, not compile-time reachability — cannot
  shrink it. The two physical-file lists were diffed byte-for-byte and are
  equal at 38. The +1,331 bytes are the deferral's own weight: `main.spl` is
  itself in the closure and deferring `.tools` costs seven dispatch wrappers.
  Those two DEFAULT rows were recentred with a recorded reason; the two
  interpreter rows keep the pre-wave baseline.
- **In-process MCP tools (B).** `_dispatch_in_process` is a single ~190-line
  if-chain over nine handler families, so any in-process tool still loads all
  nine: `tools/call simple_read` measures 128 / 1,299,669, −2.3% / −1.8%.
  Splitting that chain per family is a code move, not an import move, and was
  out of scope for an imports-only row. Open follow-up.
- **`spl_opens ≤ 1.2 × physical_files` (E).** Not met and not reachable from
  that row. Of the 444 remaining opens for `mcp-help`, 49 are
  `module_resolver/var_overlay.rs:110` re-reading one 1,309-byte file for want
  of a memo and the rest are the JIT lane's `pipeline/module_loader.rs` read
  sites, which have no parse memo. Both owners are outside L5-E's file list.
  What the row DID deliver is its stated acceptance: files read at two or more
  sites 117 → 0, one parse per physical file across both lanes.
- **Deployed closure (F).** The dedup gate is honestly RED on this host's
  deployment: 8 files, 255,668,551 closure bytes, **100,186,384 duplicated** —
  two physical copies of the 50,093,192-byte primary sharing one sha256 on
  distinct inodes instead of being hardlinked. That is the defect the gate
  exists to name, which is why it landed advisory.


### L5 entry-closure delta — all ten entries, both lanes (2026-09-12)

Re-measured by the integrator on the integrated branch with L5-A's
`scripts/perf/measure-entry-closure.shs`, `--samples 0 --verify-cold`, hermetic
`HOME`, `SIMPLE_EXECUTION_MODE`/`SIMPLE_TEST_MODE` cleared, binary
`/home/yoon/dev/simple-wave/src/compiler_rust/target/release/simple`
(51,308,600 B, sha256 `ef528c608113173c0c1aef6edb10ac17f9bf68886f34e05aff21a39c67515562`).
"Before" is `config/perf/entry_closure_baselines.sdn`, the wave baseline.
Only the PHYSICAL pair is ratcheted; `spl_opens` and `unit_spellings` move with
the seed's cross-lane read behaviour (L5-E), not with an entry's imports.

| entry | lane | files before | after | Δ files | bytes before | after | Δ bytes | owner |
|---|---|---:|---:|---:|---:|---:|---:|---|
| `cli-version` | default | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `cli-version` | interpreter | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `cli-help` | default | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `cli-help` | interpreter | 0 | 0 | — | 0 | 0 | — | native, nothing to load |
| `mcp-help` | default | 131 | **47** | **−64.1%** | 1,323,864 | **404,093** | **−69.5%** | B |
| `mcp-help` | interpreter | 131 | **46** | **−64.9%** | 1,323,864 | **378,501** | **−71.4%** | B |
| `mcp-info-call` | default | 131 | **80** | **−38.9%** | 1,323,864 | **643,244** | **−51.4%** | B |
| `mcp-info-call` | interpreter | 131 | **80** | **−38.9%** | 1,323,864 | **643,244** | **−51.4%** | B |
| `lspmcp-help` | default | 38 | 38 | +0.0% | 325,005 | 326,336 | +0.4% | C — **miss**, see below |
| `lspmcp-help` | interpreter | 38 | **6** | **−84.2%** | 325,005 | **41,252** | **−87.3%** | C |
| `lspmcp-3frame` | default | 38 | 38 | +0.0% | 325,005 | 326,336 | +0.4% | C — **miss**, see below |
| `lspmcp-3frame` | interpreter | 38 | **6** | **−84.2%** | 325,005 | **41,252** | **−87.3%** | C |
| `query-help` | default | 125 | 125 | +0.0% | 1,262,376 | 1,262,376 | +0.0% | no L5 owner (L3 landed earlier) |
| `query-help` | interpreter | 107 | 107 | +0.0% | 1,140,426 | 1,140,426 | +0.0% | no L5 owner |
| `check-help` | default | 132 | **27** | **−79.5%** | 1,302,861 | **220,550** | **−83.1%** | D |
| `check-help` | interpreter | 114 | **27** | **−76.3%** | 1,180,911 | **220,550** | **−81.3%** | D |
| `lint-one-file` | default | 387 | 309 | −20.2% | 4,307,651 | 3,767,766 | −12.5% | D — **miss**, see below |
| `lint-one-file` | interpreter | 291 | 291 | +0.0% | 3,645,845 | 3,645,816 | −0.0% | D — **miss**, see below |
| `test-one-spec` | default | 352 | 270 | −23.3% | 3,004,187 | 2,734,137 | −9.0% | G — **miss**, see below |
| `test-one-spec` | interpreter | 352 | 270 | −23.3% | 3,004,187 | 2,734,137 | −9.0% | G — **miss**, see below |

**Honest misses, none of them averaged away.**

- **`lint-one-file` (D, both lanes, target −25%).** Two blockers, both outside
  the row and both filed. (1) `lint_entry.spl` was REVERTED: leaf-importing it
  makes the whole lint/fmt/fix program stop JIT-compiling —
  `[jit-fallback] unresolved external symbol 'io_runtime_cwd': whole module
  dropped to the interpreter` — because
  `src/lib/nogc_sync_mut/sffi/system.spl:8` aliases
  `use std.io_runtime.{cwd as io_runtime_cwd}` and only the `std.io` hub was
  co-compiling that symbol into the same JIT module; under
  `SIMPLE_JIT_STRICT=1`, `simple lint --help` then exits 1 with NO output.
  (2) Even with that swap the entry has a structural floor of 301 files /
  3,388,952 bytes: 8 of the 10 `compiler.tools.lint._LintMain.*` submodules
  each pull the full 290-file / 3,316,828-byte cluster on their own, so
  splitting the `compiler.tools.lint.main` facade buys nothing. The landed
  −20.2% is one dead hub import
  (`src/compiler/35.semantics/resource_families.spl:5`), nothing more.
- **`test-one-spec` (G, target −25%).** The integrator's re-measurement is
  270 / 2,734,137 in BOTH lanes — **−23.3% / −9.0%, short of the target on
  both axes.** L5-G reported 184 / 1,757,778 from a direct shell run; that
  number did NOT reproduce here from a direct shell run, and 270 is within one
  file of the 269 the ratchet independently measured and of the 269 G itself
  measured when the measurer ran nested under `bin/simple test`. The entry is
  bimodal on the shared session-daemon path (G measured 352 vs 332 pre-fix for
  the same lane), so 184 is currently an unreproduced best case and is not
  quoted as the result. The import work is real and landed: neither the 270-
  nor the 184-file run opens any of `io/{tcp,udp,buffer,event_loop}.spl`.
- **`lspmcp-*` default lane (C).** Does not move, by mechanism, not by
  omission: the front end whole-module-compiles every top-level function in
  `main.spl` before running any of them (the pristine tree already emits
  `[CODEGEN-STUB-FALLBACK] body compilation failed for
  'handle_resource_templates_list'` on a bare `--help`), so a function-local
  `use` — which changes name scoping, not compile-time reachability — cannot
  shrink it. The two physical-file lists were diffed byte-for-byte and are
  equal at 38. The +1,331 bytes are the deferral's own weight: `main.spl` is
  itself in the closure and deferring `.tools` costs seven dispatch wrappers.
  Those two DEFAULT rows were recentred with a recorded reason; the two
  interpreter rows keep the pre-wave baseline.
- **In-process MCP tools (B).** `_dispatch_in_process` is a single ~190-line
  if-chain over nine handler families, so any in-process tool still loads all
  nine: `tools/call simple_read` measures 128 / 1,299,669, −2.3% / −1.8%.
  Splitting that chain per family is a code move, not an import move, and was
  out of scope for an imports-only row. Open follow-up.
- **`spl_opens ≤ 1.2 × physical_files` (E).** Not met and not reachable from
  that row. Of the 444 remaining opens for `mcp-help`, 49 are
  `module_resolver/var_overlay.rs:110` re-reading one 1,309-byte file for want
  of a memo and the rest are the JIT lane's `pipeline/module_loader.rs` read
  sites, which have no parse memo. Both owners are outside L5-E's file list.
  What the row DID deliver is its stated acceptance: files read at two or more
  sites 117 → 0, one parse per physical file across both lanes.
- **Deployed closure (F).** The dedup gate is honestly RED on this host's
  deployment: 8 files, 255,668,551 closure bytes, **100,186,384 duplicated** —
  two physical copies of the 50,093,192-byte primary sharing one sha256 on
  distinct inodes instead of being hardlinked. That is the defect the gate
  exists to name, which is why it landed advisory.

Observed and recorded, not fixed by this wave: `push-no-direct-rt` measures
6334 against the 6072 tracked baseline already at `7352f99898c` — but it IS
enforced, blocking, in **delta mode** (`--rev`/`--baseline-rev` against the
outgoing range's own base), so a branch that adds no new direct `rt_*` site is
admitted and one that adds any is refused; the `TODO` in the ledger belongs to
the separate bootstrap-tier `no-direct-rt` row, which is a different id and
`push_blocking: false`. Reconciliation and both measurements:
`doc/08_tracking/bug/push_no_direct_rt_red_on_main_2026-09-12.md`.
Also: `var a: [i64; 64]` rejects index assignment in the
interpreter; the pre-existing `simple lint` segfault on
`test/05_perf/text_i18n/*`; the JIT's bare enumerate over any array.

## Status 2026-09-12 17:20 — Claude session (Codex at usage limit; Claude carries EGL/GL)

Landed on `main` today (PR): interpreter perf #562 (place-aware in-place mutation kernel, string/dict/utf16 paths), loader alias units #568, `for a, b in xs` destructure #570, bootstrap Stage-2 link defects #575, bug/todo triage #576 + #578 (1,497 records: 121 resolved by re-run, 591 closed-stale, 749 left open; todo 287→244 open), guard wiring #579 (116 wired, baseline 725→607), L2 PersistentSet intersection/subset scaling #585, L10 profiling modules #589, L6 mapping-release owner + call boundary #590.

In flight (pushed or queued behind the ledger gate-sync in this PR): L5 generated-binary closure (A–G integrated: check −83 %, mcp-help −70 %, lsp-mcp interpreter −87 %, test-runner −9 %, lint −12.5 % honest miss), M2 Stage-2 receipt-content-mismatch root cause (native `Optional<struct>` unwrap resolved fields by name; receipt gate passed run 3; Stage 2 still not admitted — 180 s probe budget scrubbed by the sanity env + `storage-unavailable` behind it), bug-db shards 0–3 (P0/P1 first; ~30 resolved/closed with sabotage-proven guard specs, ~40 diagnosed as seed defects, 5 new records), todo shards 0–1 (24 implemented with specs; the locked test-db writer never worked), L3 startup (stdlib variant-root probing −21 % stats), test-runner directory-mode degrade fix, and the L7/L8 host-ABI lane.

L7/L8 (GL): Codex's ten packet tips merged by ownership into `work/l78-2026-09-12` (freeze `161f91bf`/`e71f20d`; P03 `aad948a`, P05 `a1b568e`, P07 `765f78b`, P08 `dd83e5f`, P10 `43b210b`, U01–U03). First execution of the V4 port specs: scope 8/8, affected-domain 9/9, namespace 14/14, publication 11/11, pipeline 10/10, scope_runner 8/8, gc-begin-authority 7/7; `cargo check` green; no-direct-rt unchanged. Gaps closed on top: P03 hook `issue` + scope `validate`/`close` runners + live-owner `issue`/`close`; P07 checked V3 host-probe capability (absent extern → `Unavailable`) + `begin/closure/finish/abort` runners. Not done by freeze rule: Live wiring (`_l78_pipeline_token_v4` TestDouble-only pin), hook `validate`/`close`, epoch advance for `ExpiredToken`, production activation. Three seed defects filed (wrapped trait return type, `union` reserved, global `struct Scope` shadowing).

EGL: wave branch (Codex gpu-e4-e5 24 commits + P/W/V/U/X/T/N/K + U2/X2/V2) being rebased and its +9 direct `rt_*` sites routed; Q (2-token parse), S (frozen), sosh adapter (`StmtKind` collision) and `frontend.spl` rewiring remain Codex-owned blockers.

Open lanes with no implementation: L4 memory lifecycle (agent running: bounded seed interpreter caches), L10 collector wiring (fenced), L11 complete. Push-gate note: bootstrap-tier manifest rows without ledger rows (#586, chrome-layout, test-runner-executes-bodies) blocked every push for ~1 h; this PR restores manifest == ledger (57).
