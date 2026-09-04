# Kernel Plugin Phase 0-8 and REQ-KPF Independent Audit

**Audit date:** 2026-09-03
**Audited branch head:** `49eb1be4d5a` (audit commit rebased above it)
**Verdict:** **FAIL / NOT COMPLETE**

This audit treats source presence, portable fixtures, cached output, and native
deployment evidence as distinct proof classes. It does not promote a structural
or focused result beyond the scope actually exercised.

## Fresh Narrow Checks

| Check | Result | Scope |
|---|---|---|
| Compiler closure | **PASS** | `scripts/check/check-kernel-closure.shs`: 1,979 files classified, zero unclassified, compiler-to-plugin, or K0/K1-to-P edges. |
| KPF top-level acceptance | **PASS, 5/5** | Admitted pure-Simple arm64 runtime executed `test/03_system/compiler/feature/kernel_plugin/kernel_plugin_fabric_acceptance_spec.spl`; malformed admission, zero-work lint, bounded backpressure, stale handles, and static direct/table parity passed. |
| Strict noalloc source/mutation contract | **PASS** | `strict_noalloc_proof_contract_test.shs` proves the runtime counter and real-growth negative fixture are wired and rejects disabled delta detection. This is not a long-run product allocation measurement. |
| Phase 4 remove-row mutation | **UNVERIFIED** | A fresh matrix process completed, but the detached observer did not retain its exit/output. Existing add-row PASS and the cache-busting source fix remain valid evidence; this audit does not infer the missing mutation PASS. |

No previously evidenced native ABI, performance, lifecycle, mixed-language,
tooling, or MDSOC++ check was rerun.

## Migration Phases 0-8

| Phase | Current status | Authoritative evidence | Exact remaining gap |
|---:|---|---|---|
| 0 | **PASS at required structural scope** | Plan contract at `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md:68`; fresh closure result above. | The plan's fixture SPipe remains useful regression evidence, but no source gap was found. |
| 1 | **PASS at required executable scope** | Production ABI path and admitted-runtime field/body matrix are recorded at `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md:53` and `doc/09_report/compiler/kernel_plugin_migration_phase_1_2_4_executable_matrix_2026-09-03.md:13`. | None found in Phase 1. |
| 2 | **PASS at required executable scope** | Append-only/reorder and environment-boundary execution are recorded at `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md:54`. | None found in Phase 2. |
| 3 | **PARTIAL** | Fail-closed current-schema/digest parsing is implemented and has focused 6/0 evidence at `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md:55`. | Producer-bound startup admission is absent; this is runtime/provenance evidence, not a parser source gap. |
| 4 | **PARTIAL** | Negotiation and table dispatch are implemented at `src/compiler/90.tools/lint/static_rules.spl`; core executable checks and add-row execution passed. | Fresh remove-only-row mutation output is not retained. This is one missing executable proof row; no additional source change is justified without a failing retained result. |
| 5 | **PARTIAL** | Typed/table backend dispatch and P-static relocation pass structural checks at `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md:57`. | Producer-authenticated LLVM and Cranelift bootstrap parity plus P-static edit isolation receipts are absent. Runtime/bootstrap blocker. |
| 6 | **PARTIAL** | Native ABI matrix proves matching-major and older-minor admission, wrong-major/digest rejection, one lookup, and resident dispatch; see `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md:58`. | Original APK/SFFI product admission SPipe and producer-bound load-path evidence remain absent. |
| 7 | **BLOCKED** | Source policy is atomic APK-only. One-binary dependency shape and arm64 startup observations exist at `doc/06_spec/05_perf/compiler/plugin_arch/phase7_startup_and_parity_evidence.md:17`. | No producer-created Phase 7 candidate, child APK proof, LLVM/Cranelift parity, working dynload binary, admitted resident baseline, or 20-request RSS receipt. These are runtime/deployment gaps; the available binary predates the source fixes. |
| 8 | **PARTIAL / ORDERING BLOCKED** | Deterministic ranges, compiled root dispatch, fail-closed replacement, atomic writes, and manifest identity pass the source contract at `doc/09_report/compiler/kernel_plugin_migration_phase8_completion_2026-09-03.md:7`. | Unit/integration/root-CLI execution against a current admitted runtime is absent, and Phase 7 must qualify first. |

## REQ-KPF-001..012

| Requirement | Status | Current proof | Exact remaining gap |
|---|---|---|---|
| REQ-KPF-001 placement parity | **PARTIAL** | Static direct/table semantic parity passed in the fresh 5/5 acceptance run; static/native/worker/Wasm lifecycle parity passed 4/4 in `doc/09_report/kernel_plugin_lifecycle_crash_parity_2026-09-03.md`. | One shared semantic operation corpus has not executed across static-direct, static-table, native, SMF, worker, and optional Wasm placements. |
| REQ-KPF-002 K0g closure | **PASS at structural scope** | Fresh closure is clean; the boundary contract is `doc/04_architecture/kernel_plugin/kernel_plugin_fabric_architecture.md:14`. | K0c bootstrap qualification is tracked by Phases 5/7 and is not evidence against the generic K0g closure. |
| REQ-KPF-003 SCI/query authority | **PARTIAL** | `src/os/smf/kernel_plugin/native_loader.spl:1` explicitly adapts canonical `SimpleProviderQueryV1`; admission validates and caches at `src/os/smf/kernel_plugin/native_loader.spl:117`. | End-to-end proof that every product dynamic path starts from sealed SCI, never scans/compiles at runtime, and publishes one atomic generation is incomplete. |
| REQ-KPF-004 stable ABI | **PARTIAL** | Generated C records use ABI/version-size prefixes in `src/tool/kernel_plugin_schema/generate_c.spl:58`; malformed descriptor acceptance passed and native major/minor/digest matrix passes. | Complete shared forbidden-native-type, malformed-layout, truncation/extension, endian, alignment, and unwind corpus across Simple/C/Rust/C++ is not retained. |
| REQ-KPF-005 bounded/noalloc | **PARTIAL** | Fixed runtime exposes bounded session/request state and high-water counters at `src/lib/nogc_async_mut_noalloc/kernel_plugin/fixed_runtime.spl:59`; `src/lib/nogc_async_mut_noalloc/kernel_plugin/allocation_probe.spl:17` binds activation to the runtime heap counter, and the fresh strict source/mutation contract passes. | The current producer-built Simple runtime does not yet execute this new instrumentation. Long-run product-path proof, complete capacity exhaustion, leak/fragmentation, and post-seal zero-allocation evidence remain absent. |
| REQ-KPF-006 O(1) steady state | **PASS at focused framework scope; product proof open** | Dense sealed bindings resolve once at `src/lib/nogc_sync_mut/kernel_plugin/static_registry.spl:41`; performance and complexity mutations pass in `doc/09_report/kernel_plugin_fabric_performance_2026-09-03.md`. | Representative long-lived product/provider evidence is still required; no source algorithm gap was found in the focused dispatch path. |
| REQ-KPF-007 lifecycle safety | **PASS at focused contract scope** | Failed-candidate/unload matrix is 10/10 plus 3/3 mutation in `doc/09_report/kernel_plugin_lifecycle_failed_candidate_unload_matrix_2026-09-03.md`; crash-loop/cross-placement lifecycle is 4/4 in `doc/09_report/kernel_plugin_lifecycle_crash_parity_2026-09-03.md`. | No uncovered lifecycle source behavior was found. Long-run allocation belongs to REQ-KPF-005 and product deployment to Phase 7. |
| REQ-KPF-008 generated compatibility | **PARTIAL** | Canonical generator emits Simple, C, Rust, C++, and WIT (`src/tool/kernel_plugin_schema/generate_simple.spl:18`, `generate_c.spl:18`, `generate_rust.spl:18`, `generate_cpp.spl:18`, `generate_wit.spl:72`). | Worker-wire is still a generic hand-written transport rather than a clearly generated schema projection, and the complete shared malformed/layout corpus is missing. This is the clearest remaining design/source lane, but it is not isolated enough for an audit-only patch because it changes the frozen generator contract and all SDK fixtures. |
| REQ-KPF-009 lint truth | **PARTIAL** | Coverage completeness is explicit at `src/lib/common/lint_kernel/model.spl:66`; clean is reachable only after that predicate at `src/lib/common/lint_kernel/model.spl:87`. Mixed Simple/Rust/C++ conformance and omission mutations pass 3/3. | Generated production rule catalog, normalized cross-language edits, full rust-analyzer/clangd sessions, and product-scale mixed-workspace evidence remain incomplete. |
| REQ-KPF-010 editor-neutral tooling | **PARTIAL** | Canonical result identity and stale publication guard are used at `src/app/toolingd/protocol_adapters/lsp.spl:80`; current HEAD is content-equivalent to reviewed commit `36db2266271`. Focused SVIM/toolingd/VS Code evidence is recorded in `doc/09_report/kpf_tooling_ide_canonical_conformance_2026-09-03.md`. | Browser/Wasm client parity, representative latency/RSS, and the repository-wide workspace-dependent VS Code GUI fixture remain incomplete. |
| REQ-KPF-011 extended-enum closure | **PARTIAL** | Persistent IDs, operation tables, dense tags, Complete sealing, and critical Dyn rejection are implemented at `src/compiler/00.common/dynamic_identity/kpf_closure.spl:56` and `:148`. | Final canonical schema/sealer integration and focused admitted-runtime execution remain missing. |
| REQ-KPF-012 MDSOC++ | **PARTIAL** | Capsule sealing and upgrade/rollback retention are implemented at `src/lib/mdsocpp/pilot/ide_tooling.spl:182` and `:222`; focused pilot evidence is 8/8. | One broader product upgrade/rollback deployment, fresh admitted-runtime evidence, and product resource/performance qualification remain absent. |

## Source Gaps vs Runtime-Only Blockers

### Source/design work still required

1. Generate or formally derive worker-wire projections from the canonical KPF schema and extend the shared cross-language malformed/layout corpus (REQ-KPF-008).
2. Finish generated lint-rule catalog and normalized cross-language fix/edit ownership (REQ-KPF-009).
3. Complete final extended-enum/KPF schema-sealer integration (REQ-KPF-011).
4. Repair the repository-wide VS Code workspace fixture and add browser/Wasm client parity (REQ-KPF-010).

### Runtime/deployment evidence only

1. Producer-authenticated current arm64 compiler and Stage2-to-Stage3 lineage.
2. LLVM/Cranelift native bootstrap parity and P-static edit isolation.
3. Phase 7 current-binary dynload, child APK, one-binary candidate, resident RSS, and 20-request growth.
4. Phase 8 executable unit/integration/root-CLI matrix after Phase 7.
5. Native x86_64, universal assembly/execution, distribution signing, notarization, and immutable promotion.

## Conclusion

**STATUS: FAIL / NOT COMPLETE.** Phases 0-2 are proved at their required scope;
Phase 4 has one unretained mutation row; Phases 3 and 5-8 remain partial or
blocked. REQ-KPF-002 and focused REQ-KPF-006/007 contracts pass, while the
remaining requirements lack either full cross-placement/product evidence or
specific source/design work listed above. No production change was made because
no isolated failing source defect was established by this audit.
