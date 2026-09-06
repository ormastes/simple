<!-- codex-design -->
# Staged Parallel Implementation Plan

## Scope and authority

This plan implements selected **Feature Option C** and **NFR Option 1** without narrowing the six-phase end state. It is a task/merge plan, not evidence that any phase is implemented. Pure-Simple compiler, library, and application owners remain authoritative. Release, version bump, tag, and push are out of scope.

The implementation must preserve these boundaries:

- source diagnostics describe actionable source problems;
- optimizer remarks describe passed, missed, analysis, and failure outcomes;
- compiler-integrity defects fail compiler CI rather than becoming user lints;
- uncertain facts fail closed as `Unknown` or `AnalysisIncomplete(reason)`;
- semantic transforms require legality, lifetime, alias, effect, ordering, safety, and profitability proof;
- only one lane owns each shared interface or file during a merge wave.

## Shared names frozen before sidecars start

The merge owner defines these interfaces in the contract wave. Sidecars consume them and must not create competing variants:

- `PassStatus`, `PassExpectation`, `BackendDelegation`
- `PassRunRecord`, `PassRejectionReason`, `EffectivePipelineRecord`
- `PerfRuleId`, `PerfDiagnostic`, `OptimizationRemark`, `RemarkKind`
- `PerfFactKey`, `PerfFacts`, `FactPreservation`, `FactInvalidation`
- `LoopForest`, `LoopFact`, `InductionFact`, `RegionAliasFacts`, `MemoryVersionFacts`
- `CostExpr`, `OperationSummary`, `PerfSummary`, `AnalysisIncomplete`
- `CowUniqueness`, `CowEvidence`, `CollectionPlan`

Scenario/manual helper names are fixed as:

- `step("Inspect the effective optimizer pipeline")`
- `step("Run a positive pass activation witness")`
- `step("Run a negative legality witness")`
- `step("Check typed performance diagnostics")`
- `step("Inspect a missed optimization remark")`
- `step("Compare complexity summaries")`
- `step("Rank findings using profile evidence")`
- setup helper `prepare_performance_audit_fixture`
- checker helpers `check_pipeline_truth`, `check_diagnostic_contract`, `check_summary_diff`, `check_profile_ranking`

Unimplemented executable scenarios must fail fast with `assert(false)` or `fail(...)`; placeholder passes, empty bodies, and tautological assertions are forbidden.

## Baseline-first admission

Before source edits, the merge owner records current worktree ownership and admits one native pure-Simple binary. Do not use the Rust seed. Baseline commands are run once, with bounded output captured under `build/test-artifacts/simple_compiler_performance_memory_efficiency/baseline/`:

```sh
jj status
jj log -r @ -n 1 --no-graph
sha256sum bin/release/*/simple
bin/simple check src/compiler
bin/simple check src/lib
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
bin/simple test test/03_system/compiler/optimizer_system_spec.spl --mode=interpreter
bin/simple test test/03_system/app/lint_cli_contract_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/check/check-lint-cost-budget.shs
sh scripts/check/check-cow-alias-hotpath.shs
sh scripts/check/check-mcp-lsp-nfr-evidence.shs
sh scripts/audit/direct-env-runtime-guard.shs --working
```

For performance measurements, record command, commit, binary path/hash/stage/provenance, target, fixture hash/size, warmup/repetitions, elapsed distribution, peak RSS, counters, and fallback state. A failed or unavailable baseline remains explicit; it is not normalized into PASS. Re-running unchanged green commands is prohibited.

## Dependency graph

```text
W0 baseline + ownership map
 |
 v
W1 vector containment + shared contracts
 |------------------------|
 v                        v
W2 frontend/diagnostics   W3 MIR fact foundation
 |                        |
 |-----------+------------|
             v
W4 first-release typed rules + truthful remarks
 |------------------------|
 v                        v
W5 CollectionPlan/COW     W6 pass-by-pass rehabilitation
 |                        |
 |-----------+------------|
             v
W7 interprocedural CostSummary + .sperf CI
             |
             v
W8 .sprof-v2 + empirical/profile analysis
             |
             v
W9 tools/hot-path repair + MCP/LSP/package evidence
             |
             v
W10 docs/manual/refactor + production verification
```

W2 and W3 may run in parallel only after W1 lands. W5 and W6 may run in parallel only when their file manifests are disjoint. W7 consumes stable W2/W3/W4 contracts. W8 consumes W7’s stable identities and formats. W9 is late because it validates the integrated cache/index/invalidation behavior.

## Parallel ownership lanes

### W0 — Baseline and inventory

**Owner:** merge owner/highest-capability agent. **Sidecars:** read-only inventory lanes only.

Deliverables:

- admitted binary receipt and baseline table;
- dirty-file ownership map preserving unrelated agent work;
- requirement-to-evidence matrix for REQ-001–REQ-025 and NFR-001–NFR-015;
- exact changed-file manifests reserved for each following wave.

Likely evidence files only:

- `build/test-artifacts/simple_compiler_performance_memory_efficiency/baseline/**`
- `.spipe/simple_compiler_performance_memory_efficiency/**`

Gate: no implementation starts until unsafe shared files have one owner and existing failures are classified.

### W1 — Safety containment and truthful optimizer contracts

**Lane W1-A, single owner: vector containment.** Likely files:

- `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl`
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl`
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_validate.spl`
- `src/compiler/60.mir_opt/mir_opt/_AutoVectorize/rewrite.spl`
- `src/compiler/60.mir_opt/optimizer_manifest.spl`
- `src/compiler/60.mir_opt/optimization_passes.spl`

Containment lands first: unsafe rewriting is removed from the effective pipeline until exact induction, `+1` step, dominance, trip-count, dependence, alias, effect, and target legality are proven. Analysis/missed remarks may remain.

**Lane W1-B, single contract owner:** pass contracts and telemetry. Likely files:

- `src/compiler/00.common/structural_contracts/optimizer.spl`
- `src/compiler/60.mir_opt/optimizer_manifest.spl`
- `src/compiler/60.mir_opt/optimizer_plugin.spl`
- `src/compiler/60.mir_opt/optimization_passes.spl`
- `src/compiler/60.mir_opt/_OptimizationPasses/engine.spl`
- `src/compiler/60.mir_opt/mir_opt_integration.spl`
- `src/compiler/70.backend/backend/optimization_passes.spl`

W1-B owns all shared pass enums and records. Other lanes submit requested contract changes to W1-B rather than editing these files concurrently.

**Lane W1-C, tests only:** positive/negative sentinel fixtures and pipeline truth. Likely files:

- `src/compiler/60.mir_opt/optimization_passes.spipe`
- `test/03_system/compiler/optimizer_system_spec.spl`
- new focused fixtures under `test/02_integration/compiler/optimizer/`
- new system spec under `test/03_system/app/compiler/feature/`

Gate: effective pipeline output is deterministic; unknown names/missing required facts fail closed; active transforms have non-vacuous sentinels; changed passes run the verifier; no unsafe vector rewrite remains advertised.

### W2 — Shared frontend and diagnostic ownership

**Lane W2-A, frontend session owner:** reuse parsed/typed artifacts and preserve spans. Likely files:

- `src/compiler/80.driver/**`
- `src/compiler/20.hir/**`
- `src/compiler/35.semantics/lint_cross_ref.spl`
- `src/compiler/90.tools/lint/main.spl`
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`
- `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
- `src/app/simple_lsp_mcp/main.spl`
- `src/app/simple_lsp_mcp/tools.spl`
- `src/app/mcp/main_lazy_query_tools.spl`

One agent owns cache identity/invalidation interfaces. MCP/LSP lanes consume them through ports and do not duplicate parser caches.

**Lane W2-B, diagnostic contract owner:** likely files:

- new `src/compiler/35.semantics/perf/**`
- `src/compiler/35.semantics/lint/__init__.spl`
- `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
- `src/compiler/90.tools/lint/_LintMain/lint_checks.spl`

This lane owns `PerfRuleId`, `PerfDiagnostic`, remark separation, versioned text/JSON, stable ordering, confidence/tier/resource evidence, suppression, and fix applicability. Existing COLL compatibility is frozen until baselined.

**Lane W2-C, tests only:** `test/03_system/app/lint_cli_contract_spec.spl`, new diagnostic fixtures/specs, JSONL purity tests, and warm reuse probes.

Gate: one artifact owner per revision; warm lint/LSP has zero recursive scans and compiler subprocesses; existing COLL ordering/severity/exit/suppression behavior is preserved.

### W3 — Shared MIR facts

The primary model defines interfaces first. Sidecars own disjoint implementations:

- **W3-A CFG/dominance:** new `src/compiler/60.mir_opt/analysis/cfg.spl`, `dominators.spl`, `post_dominators.spl`, `rpo.spl`.
- **W3-B loop forest/SCEV-lite:** replace/consolidate `src/compiler/60.mir_opt/mir_opt/loop_detect.spl`; new `analysis/loop_forest.spl`, `induction.spl`, `ranges.spl`.
- **W3-C def-use/liveness:** new `analysis/def_use.spl`, `liveness.spl`; remove repeated nested def/use pairing in consumers.
- **W3-D memory/alias/effects:** new `analysis/regions.spl`, `memory_versions.spl`, `memory_ssa_lite.spl`; integrate `src/compiler/50.mir/mir_effects.spl`, `src/compiler/00.common/effects*.spl`, and `src/compiler/35.semantics/effect_verifier.spl`.
- **W3-E escape/ownership:** harden `src/compiler/55.borrow/gc_analysis/escape.spl` and add proof-reason tests; unresolved flows remain escaping/unknown.
- **W3-F fact cache/invalidation, single owner:** new `analysis/perf_facts.spl`, `analysis/invalidation.spl`, `analysis/__init__.spl`.

No W3 sidecar edits another sidecar’s implementation file. W3-F alone edits shared exports and integration wiring after reviewing each result.

Gate: CFG/predecessors/RPO build once per function revision; real preheaders/latches/exits and dominance are never inferred from block IDs; analyses expose build/cache/rebuild/budget metrics; unknown calls/effects/aliases fail closed.

### W4 — First-release typed diagnostics and remarks

After W2 and W3 merge, sidecars implement disjoint rule modules under `src/compiler/35.semantics/perf/rules/`:

- **W4-A:** `copy_cow.spl` — COPY001, COPY002, COPY003, COPY004, COPY005.
- **W4-B:** `collection_iteration.spl` — multiple enumeration, nested linear lookup, COLL009/COLL010 foundations.
- **W4-C:** `materialization_capacity.spl` — repeated sort/materialization, missing reserve, duplicate lookup.
- **W4-D:** `layout_stack.spl` — large parameters/stack objects and LAYOUT001–003 using target layout.
- **W4-E:** `invariant_allocation.spl` — improved invariant work and allocation/COW remarks.
- **W4-F, compatibility/test owner:** central registration, stable ordering, profiles, suppressions, fixes, and old COLL parity fixtures.

Each rule module owns matching unit/integration fixtures. W4-F alone edits central registries. Fixes that change borrowing/view semantics remain non-machine-applicable until ownership/lifetime proof exists.

Gate: high-confidence first-release catalog has positive, suppression, fixed-small-bound, and unknown-proof cases; no new rule reparses or independently walks all HIR.

### W5 — CollectionPlan and first-class COW

- **W5-A operation/resource contracts:** new `src/compiler/40.collection_plan/operation_summary.spl`, `cost_expr.spl`, `cardinality.spl`.
- **W5-B plan extraction/planning:** new `src/compiler/40.collection_plan/collection_plan.spl`, `extract.spl`, `planner.spl`, integrating `src/compiler/10.frontend/desugar/collection_desugar.spl`.
- **W5-C proven lowering:** integrate `src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl`, `collection_opt_patterns.spl`, `collection_opt.spl`.
- **W5-D COW evidence:** `src/compiler/50.mir/mir_instructions.spl`, `mir_instruction_kinds.spl`, `mir_call_ownership.spl`, and new `src/compiler/55.borrow/cow/**`.

W5-C must not place hoisted work in a loop header in lieu of a real preheader. Zero-trip, exception/destruction order, equality/order, alias, callback effect, and allocation timing are explicit gates.

Gate: only pure proven pipelines transform; unknown semantic substitutions reject with precise remarks; COW elimination requires ownership, last-use, alias, effect, destruction-order, and lifetime proof.

### W6 — Pass-by-pass rehabilitation

Each pass is a separate mini-lane and commit; never bulk-activate. Order:

1. `const_fold.spl`
2. `copy_prop.spl`
3. `dce.spl`
4. `cse.spl`
5. `loop_licm.spl` / `loop_opt.spl`
6. exact reserve insertion through CollectionPlan
7. `bounds_check_elim.spl`
8. stack promotion after W3-E
9. `tco.spl`
10. `gvn.spl`

Later guarded lanes include `string_builder_opt.spl`, `loop_strength.spl`, unrolling, general fusion, and vector rewriting. A mini-lane may change only its pass, dedicated fixtures, and W1-B-owned manifest through a reviewed integration patch.

Required gate per pass: activation/non-candidate witness, rejection reasons, verifier, semantic differential run, idempotence, malformed/irreducible CFG, overflow/FP/trap/zero-trip/alias/unsafe-pointer cases as applicable, target/backend matrix, and performance witness. Failure leaves the pass honestly non-active.

### W7 — Interprocedural summaries and `.sperf`

- **W7-A summary model/cache:** new `src/compiler/65.perf_summary/**` with stable fingerprint, assumptions, confidence, unknown reasons, bounded SCC fixed point, and precise caller invalidation.
- **W7-B full rule catalog:** remaining COLL011–018, loop/offload/stride/vectorization, ALLOC/ESCAPE/RETENTION/MEM/CACHE/STACK rules in disjoint rule files.
- **W7-C `.sperf` codec/diff/CLI:** new `src/compiler/90.tools/perf/sperf_*.spl`, extend `src/compiler/90.tools/perf/optimizer.spl` and driver command wiring.
- **W7-D CI tests:** stable identity, deterministic serialization, degree/resource regression policy, known-to-unknown, timeout, cancellation, and corrupt/stale inputs.

Gate: analysis caps are explicit; timeout/unsupported/cancellation produces incomplete evidence; CI rejects only confident selected regressions.

### W8 — `.sprof-v2`, empirical curves, and profile ranking

- **W8-A schema/codec:** extend existing profile owners, preserving v1 compatibility and hot-path no-I/O/no-allocation when disabled.
- **W8-B instrumentation:** optional loop/cardinality/allocation/copy/COW/escape/suspension/remark records.
- **W8-C curve workflow:** bounded sizes/repetitions, fixed-startup subtraction, confidence output, and time/allocation/COW metrics.
- **W8-D ranking:** correlate stable sites/summaries and rank estimated waste without using profiles as semantic proof.

Likely files include `src/compiler/90.tools/perf/profiler.spl`, `src/compiler/85.mdsoc/adapters/in/profiler_adapter.spl`, `src/compiler/20.hir/hir_lowering/hir_phase_profile.spl`, `src/app/optimize/**`, and matching system specs under `test/03_system/app/optimize/feature/`.

Gate: disabled path performs no hot I/O/allocation; schema is versioned/deterministic; overhead and sampling/threshold behavior meet NFR-012.

### W9 — Compiler/tool hot-path repair

Profile before changing. Assign one owner per hotspot:

- lint parse/session reuse;
- repeated CFG/fact construction;
- worklist slicing/linear membership/array concatenation;
- textual expression keys in CSE/GVN replaced with structural keys;
- redundant full-tree reads/scans;
- MCP/LSP startup and warm request cache/index/invalidation;
- production wrappers execute cached compiled artifacts.

Likely files include `src/compiler/90.tools/lint/**`, `src/compiler/60.mir_opt/**`, `src/app/mcp/**`, `src/app/simple_lsp_mcp/**`, `scripts/check/check-lint-cost-budget.shs`, `scripts/check/check-mcp-lsp-nfr-evidence.shs`, and packaging wrappers only if measured evidence requires them.

Gate: NFR-003/004/005/006/007/013 measurements meet budgets or a concrete bug/TODO retains the unmet criterion. No cold maintenance scan is changed without evidence.

### W10 — System evidence, manuals, refactor, verification

**Executable spec owner:** one best-model agent owns shared scenario helpers and the canonical spec. Likely artifacts:

- `test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl`
- `doc/06_spec/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.md`
- `doc/03_plan/sys_test/simple_compiler_performance_memory_efficiency.md`

**Manual/docs owner:** updates architecture/TLDR, detail design, compiler/lint/perf guides, expert pages, and workflow instructions changed by implementation. It runs docgen once, reads the result as an operator manual, fixes `@step`/`@prev`/`@inline`/capture visibility, and requires zero stubs.

**Final reviewer:** best available normal/highest-capability model, not a lower-model sidecar. It performs requirement-by-requirement evidence review and owns no feature source changes during review.

## No-overlap merge sequence

1. Freeze manifests and land W1-A containment.
2. Land W1-B contracts; rebase W1-C tests and land them.
3. Land W2-A frontend ownership, then W2-B diagnostic model, then W2-C tests.
4. Land W3-A through W3-E as implementation-only modules; W3-F integrates/exports them last.
5. Land W4 rule modules; W4-F integrates registries/tests last.
6. Land W5 contracts/extraction before lowering/COW consumers.
7. Land each W6 pass separately in rehabilitation order.
8. Land W7 summary core, full rule modules, then `.sperf` CLI/CI.
9. Land W8 schema before instrumentation/curves/ranking.
10. Land W9 one measured hotspot at a time.
11. Land W10 specs/manual/docs, then final review fixes.

If two lanes need the same file, the lower-level lane supplies a patch request; the declared owner applies it after the lane result is reviewed. Never merge by accepting both sides of a conflicted shared contract.

## Risk gates and stop rules

- **Miscompile gate:** any semantic differential mismatch disables the transform immediately and preserves before/after evidence.
- **Vector gate:** rewriting remains excluded until all REQ-001 proofs and target evidence pass.
- **Escape gate:** Unknown never becomes NoEscape; stack promotion remains disabled until REQ-014 is complete.
- **Effect/alias gate:** unknown behavior is top/conservative; it cannot authorize movement/fusion.
- **Zero-trip gate:** hoisting/movement proves zero-trip semantics, speculation/traps, and destruction order.
- **Compatibility gate:** typed COLL migration cannot silently alter severity, ordering, suppressions, fixes, exit status, JSON, or spans.
- **Cache gate:** every long-lived cache is revision-bound, bounded, observable, and invalidated deterministically.
- **Budget gate:** performance evidence uses the same admitted binary and fixed fixtures; missing provenance is no evidence.
- **Facade gate:** working and staged direct-env/runtime audits must pass; no local raw process/env shortcut is accepted.
- **Runaway gate:** one acceptance criterion is checked once unchanged per session. Maximum three fix/verify cycles per feature slice. On cycle three, stop, retain failure evidence and exact resume command, and report the unmet requirement. Never repeat an identical command expecting a different outcome.

## Focused verification commands

Select commands according to changed scope and execute each unchanged gate once:

```sh
bin/simple check src/compiler
bin/simple check src/lib
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
bin/simple lint <changed-.spl-files>
bin/simple duplicate-check <owned-dir> --mode token --min-lines 5
bin/simple test test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl --mode=interpreter
bin/simple test test/03_system/compiler/optimizer_system_spec.spl --mode=interpreter
bin/simple test test/03_system/app/lint_cli_contract_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/check/check-lint-cost-budget.shs
sh scripts/check/check-cow-alias-hotpath.shs
sh scripts/check/check-mcp-lsp-nfr-evidence.shs
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
find doc/06_spec -name '*_spec.spl' | wc -l
```

If MCP/LSP native/package paths change, also run the required native-build closures and isolated package smoke defined by repository policy. Before release handoff (outside this plan’s scope), verification additionally requires the canonical whole-suite evidence.

## Completion evidence

The program is complete only when authoritative evidence proves every selected requirement, not merely when files exist:

- REQ-001–REQ-005: effective-pipeline records, sentinels, rejection reasons, verifier and differential fixtures;
- REQ-006–REQ-009: session/cache counters, span/compatibility fixtures, deterministic diagnostic text/JSON;
- REQ-010–REQ-011: each rule has positive, negative/suppression, error-path, placement/action, and configuration evidence;
- REQ-012–REQ-019: bounded/canonical summaries, fact construction/invalidation counters, fail-closed cases, semantic transforms, and SCC invalidation tests;
- REQ-020–REQ-022: `.sperf`, `.sprof-v2`, CI/curve/profile fixtures with provenance and confidence;
- REQ-023–REQ-024: before/after measurements, hot-path scan/subprocess evidence, pure-Simple ownership, and facade audits;
- REQ-025: current research, requirements, NFRs, architecture/TLDR, designs, plans, executable SSpec, generated manual, guides, expert pages, and retained bug records;
- NFR-001–NFR-015: pinned-corpus timing/RSS distributions, deterministic output, bounded caches/analysis, portability review, startup/request evidence, and three-cycle convergence log.

Unavailable hardware/profile rows remain explicitly blocked with prerequisites, retained artifacts, exact resume command, owner, and final reviewer. They cannot be silently skipped or promoted to PASS. Final status is PASS only after the highest-capability reviewer maps every requirement to current authoritative evidence and finds no missing or indirect proof.
