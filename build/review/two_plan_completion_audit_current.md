# Independent Two-Plan Completion Audit

**Audit date:** 2026-09-03
**Audited HEAD:** `aa7370895d332a7ee79633f18f0678743d355c47`
**Scope:**

- `doc/03_plan/compiler/macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`
- `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`

**Overall verdict:** **NOT COMPLETE.** Both plans have substantial implemented
and mutation-tested foundations, but current HEAD does not satisfy either
plan's complete acceptance contract. This audit does not treat source presence,
portable self-tests, prior contributor reports, or an unrelated release binary
as native/bootstrap qualification.

## Classification Rules

- **PROVED:** the exact required behavior has current, authoritative executable
  or immutable artifact evidence at this HEAD.
- **PARTIAL:** some required source and focused evidence exist, but at least one
  required dimension or acceptance row is absent or contradicted.
- **BLOCKED:** implementation/checking exists, but the required proof cannot run
  because a prerequisite artifact, architecture, tool, or admitted producer
  chain is unavailable.
- **MISSING:** required implementation or proof is absent, or a current
  authoritative checker contradicts a prior pass claim.

## Audit Commands and Current Results

| Command | Result | Meaning |
|---|---|---|
| `scripts/check/check-kernel-plugin-migration-evidence-matrix.shs` | **BLOCKED**, exit 2 | Phase 1 ABI behavior cannot run with `bin/release/simple`. |
| `scripts/check/check-kernel-closure.shs` | **FAIL**, exit 1 | 33 forbidden compiler/K0/K1-to-plugin imports; phases 0 and 5 cannot claim structural closure. |
| `scripts/check/check-stage4-runtime-abi-gate.shs --self-test` | **PASS** | Portable fail-closed Stage4 contract only; no real candidate admitted. |
| `scripts/check/check-macos-bootstrap-receipt.shs --selftest` | **BLOCKED**, exit 1 | Required `bin/simple` native producer is unavailable in this checkout. |
| `test/01_unit/scripts/macos_reverse_reference_m4_contract_test.shs` | **PASS** | Portable M4 contract, eight fixtures, strict `Results:` parsing, mutations. |
| `test/01_unit/scripts/macos_m5_hermetic_snapshot_wrapper_test.shs` | **PASS** | Portable M5 snapshot contract; 5/5 mutations rejected. |
| `scripts/check/check-macos-reverse-reference-owner-publication-mutations.shs` | **PASS** | Reverse-reference publication mutation contract. |
| `test/01_unit/scripts/stage2_parent_receipt_producer_test.shs` | **PASS** | Stage2 producer wiring and mutation rejection; not a real Stage2 build. |
| `scripts/check/kernel-plugin-fabric/check-strict-noalloc-instrumentation.shs` | **PASS** | Native allocator interposition: clean=0, mutation=23. |
| `scripts/check/kernel-plugin-fabric/benchmark-performance-capacity.shs` | **FAIL**, exit 20 | Current benchmark computes unsigned negative overhead as `18446744073709539006`; current performance gate is not reproducibly green. |
| `scripts/check/kernel-plugin-fabric/benchmark-performance-capacity-mutation.shs` | **PASS** | Threshold/complexity mutations reject. |
| `find doc/06_spec -name '*_spec.spl'` | no output | Executable SPipe files are not misplaced under documentation. |

## Plan A — macOS Bootstrap and Reverse-Reference Harmonization

### Milestones M0–M5

| Deliverable | Classification | Exact evidence and gap |
|---|---|---|
| **M0 — Freeze baselines and receipts** | **PARTIAL / BLOCKED** | Receipt validation and producer-side Stage2 publication exist in `scripts/check/check-macos-bootstrap-receipt.shs` and `scripts/bootstrap/publish-stage2-parent-receipts.shs`; mutation test passes. No admitted arm64+x86_64 cold Phase2/3 baseline pair exists. Current receipt command blocks on unavailable `bin/simple`. |
| **M1 — Target-key and linker correctness** | **PARTIAL / BLOCKED** | Target/SDK/deployment/provider/linker identity is represented by `src/app/build/targets/action_identity.spl`, `src/compiler/00.common/cache/darwin_runtime_provider_manifest.spl`, and Darwin linker code. Portable negative evidence exists; no retained qualified native pair proves requested slices and link commands. |
| **M2 — Reverse-reference projection receipts** | **PARTIAL** | `src/compiler/00.common/cache/reverse_reference_facts.spl`, `src/compiler/80.driver/cache/reverse_reference_receipt.spl`, and owner-publication mutation gate exist. Current mutation gate passes. Required native incremental executions and full SPipe execution remain absent/blocked. |
| **M3 — Phase2→3 compatible reuse** | **PARTIAL / BLOCKED** | Compatibility manifest/admission sources and focused specs exist; Stage2 producer receipt wiring now exists. No admitted native Phase2→3 reuse receipt, rejection ledger, or normalized clean-versus-reused output comparison exists. |
| **M4 — Native per-architecture qualification** | **PARTIAL / BLOCKED** | Portable M4 contract passes and arm64 standalone startup/RSS evidence exists in `doc/09_report/macos_bootstrap_reverse_reference_native_evidence_2026-09-03.md`. That report explicitly lacks Stage2/3 provenance. There is no admitted arm64 M4 row and no x86_64 row. |
| **M5 — Universal packaging and promotion** | **PARTIAL / BLOCKED** | Hermetic snapshot wrapper passes 5/5 mutation rejection. No two admitted thin Phase3 slices, cross-architecture native execution, distribution signature, notarization, or promote-without-rebuild receipt exists. |

### Required Reverse-Reference Projections 1–10

| # | Required projection | Classification | Evidence |
|---:|---|---|---|
| 1 | Direct import/exported-name used entries | **PARTIAL** | Publication checker and `reverse_reference_facts.spl` cover the family; no admitted native edit receipt. |
| 2 | Trait/type implementation and method candidates | **PARTIAL** | Owner-publication mutation matrix covers trait publication; runtime/native causal fixture remains unqualified. |
| 3 | Unresolved method leaf/call-site candidates | **PARTIAL** | Structural owner publication is mutation-tested; no native boundary/negative receipt. |
| 4 | Annotation consumers | **PARTIAL** | Structural publication is mutation-tested; no native causal execution. |
| 5 | Generic definition/specialization consumers | **PARTIAL** | Structural publication is mutation-tested; no native causal execution. |
| 6 | AOP selector/read-field/advice/target consumers | **PARTIAL** | Structural publication is mutation-tested and conservative fallback retained; native incremental proof absent. |
| 7 | Runtime operation/provider consumers | **PARTIAL** | Structural publication is mutation-tested; provider-change native invalidation receipt absent. |
| 8 | Initializer DAG dependents | **PARTIAL** | Structural publication is mutation-tested; native incremental proof absent. |
| 9 | Module/SCC MIR and object consumers | **PARTIAL** | Receipt types and closure sources exist; no admitted no-op/private/interface native run. |
| 10 | Emitted-symbol relocation consumers | **PARTIAL** | Structural publication is mutation-tested; native linker-reachability proof absent. |

All ten families have structural publication evidence, but none is **PROVED**
against the plan's native Phase2→3 acceptance scope.

### Acceptance Gates

| Gate | Classification | Exact evidence and unmet requirement |
|---|---|---|
| Source/provenance | **BLOCKED** | Audited checkout is clean, but no immutable admitted Phase2+Phase3 receipt pair binds compiler/provider/SDK/target/command hashes. Standalone arm64 binary explicitly lacks provenance. |
| Phase2 | **BLOCKED** | Producer publisher wiring passes its mutation test; no current admitted native Phase2 on both architectures starts, compiles, and passes receiver/provider contracts. |
| Phase3 | **BLOCKED** | No Phase3 produced by an admitted Phase2 with complete lineage and focused contract results. |
| Incremental no-op | **MISSING** | No retained native receipt proves zero parse/lower/emit and zero link under unchanged ordered inputs. |
| Private-body edit | **PARTIAL / BLOCKED** | Structural dependency model exists; no native receipt proves only edited module and MIR/codegen consumers rebuild with normalized equality. |
| Interface edit | **PARTIAL / BLOCKED** | Exact reverse-reference structures and fail-closed fallback exist; no admitted native invalidation trace. |
| Cross-phase reuse | **PARTIAL / BLOCKED** | Exact compatibility admission exists and mutation coverage is reported; no native hit/rejection ledger or output parity evidence. |
| Concurrency | **PARTIAL** | Separate mutable lanes and exclusive immutable publication exist. Shared writable CAS/P4 identical/conflicting writer, pinned-reader, crash-recovery, and GC evidence is not delivered. |
| Memory/performance | **BLOCKED** | Standalone arm64 process measured 0.06 s cold and 0.46% RSS growth, but it is not an admitted long-lived per-architecture baseline. x86_64 baseline and qualifying receipts are absent. |
| Mach-O | **PARTIAL / BLOCKED** | Standalone binary is thin arm64 Mach-O with ad-hoc signature. No admitted x86_64 thin candidate and no exact two-slice universal artifact exist. |
| Tools | **BLOCKED** | No producer-bound Phase2/3 full CLI/test-runner plus MCP/LSP startup/request PASS rows on both architectures. |
| Release | **BLOCKED** | Native per-architecture gates, universal execution, distribution signing/notarization, and immutable promotion are absent. |

### Plan A Verdict

No M0–M5 milestone or release acceptance gate is fully proved at the plan's
required two-architecture/native scope. The strongest current result is
portable structural/mutation evidence plus a non-admitted arm64 runtime
measurement. Plan A remains **NOT COMPLETE**.

## Plan B — Kernel + Pluggable Migration

### Phases 0–8

| Phase | Classification | Exact evidence and gap |
|---:|---|---|
| 0 — Partition declaration | **MISSING / CURRENTLY FAILING** | `scripts/check/check-kernel-closure.shs` currently reports 33 forbidden imports, including `src/compiler/35.semantics/layer_call_wiring.spl` to tooling and numerous compiler backend files to `src/plugins/backend_*`. This directly contradicts the plan's earlier structural-PASS row. |
| 1 — Real ABI digest | **PARTIAL / BLOCKED** | `src/compiler/20.hir/abi_interface.spl` and production HIR wiring exist. The authoritative phase matrix blocks because ABI behavior cannot execute with current `bin/release/simple`; field/body mutation behavior is therefore not currently proved. |
| 2 — Param objects and lint | **PARTIAL / BLOCKED** | Typed `AspectParamsV1`, app-boundary environment projection, and evolution checker/spec exist. Required executable SPipe and complete env-to-record proof remain blocked. |
| 3 — Manifest identity | **PARTIAL** | Current schema-35 checked parsing, identity fields, and focused 6/0 evidence are recorded. Startup/native admission remains blocked; no complete product startup receipt at this HEAD. |
| 4 — Lint table seam | **PARTIAL / BLOCKED** | `lint_rule_api.spl`, `static_rules.spl`, generated KPF lint records, semantic check, and output projections exist. Required bootstrap receipt and complete rule-table mutation execution remain unqualified. |
| 5 — Backend port/P-static relocation | **MISSING / CURRENTLY FAILING** | KPF native/worker adapters and retained sessions exist, but the closure checker reports 32 compiler/K1-to-backend-plugin imports. Required LLVM and Cranelift bootstrap rows and plugin-edit/no-kernel-rebuild native receipt are absent. |
| 6 — APK/SFFI negotiation | **PARTIAL / BLOCKED** | Negotiation/admission sources, ABI-v1 policy, native loader, signature/trust checks, and focused structural tests exist. No retained real native dynamic-library compatibility matrix proves old-minor acceptance and wrong-major rejection in production. |
| 7 — Aspects as packs/kernel closure | **PARTIAL / BLOCKED** | APK-only policy, Phase7 checker/specs, KPF lifecycle/worker/shared-memory infrastructure, and mutation gates exist. One-binary, native dynload, parity, startup, admitted RSS, and both architecture rows remain blocked; failed phase-0 closure also prevents the claimed kernel closure. |
| 8 — Package ranges | **PARTIAL / ORDERING BLOCKED** | Range parsing, deterministic lock/update paths, policy binding, and specs/manuals exist. Phase 7 is not qualified, and the complete root-CLI executable matrix is not currently authoritative. |

### Selected Policy Deliverables

| Policy | Classification | Evidence |
|---|---|---|
| LLVM default + explicit Cranelift K1 | **PARTIAL** | Machine-readable authority and dispatch exist; both admitted native bootstrap rows are absent and closure currently fails. |
| ABI v1 now | **PARTIAL** | ABI-v1 records, generated C/Simple/Rust/C++ bindings, compatibility checks, and SDK tests exist; full production APK/SFFI native matrix remains blocked. |
| Canonical `simple.sdn` | **PARTIAL** | Parser/admission binding exists; complete startup/native admission receipt is absent. |
| Atomic APK-only coverage | **PARTIAL** | Policy rejects dual/source-rewrite paths structurally; one-binary native execution/parity evidence is absent. |
| Baseline-relative RSS limits | **BLOCKED** | No admitted architecture-matched baseline and 20-request receipt pair. Standalone arm64 startup evidence is not admissible for this gate. |

### Phase Acceptance Deliverables

| Deliverable | Classification | Evidence |
|---|---|---|
| Phase 0 clean classification and zero forbidden edges | **MISSING** | Current closure checker: 1973 classified, 0 unclassified, **33 forbidden imports**. |
| Phase 1 field-sensitive/body-insensitive ABI digest | **PARTIAL / BLOCKED** | Source and specs exist; authoritative matrix cannot execute the behavior. |
| Phase 2 no driver env reads and append-only params | **PARTIAL** | Structural checker/source exists; executable round-trip and full mutation row not authoritative. |
| Phase 3 fail-closed manifest identity | **PARTIAL** | Focused parsing evidence exists; product startup/native row absent. |
| Phase 4 add-one-file/table-row lint seam and negotiation | **PARTIAL** | Table/provider infrastructure exists; required bootstrap receipt and complete mutation execution absent. |
| Phase 5 LLVM+Cranelift bootstrap and plugin edit isolation | **MISSING / BLOCKED** | Current closure fails and no admitted bootstrap/plugin-edit cache-key receipt exists. |
| Phase 6 major reject/older-minor accept with unchanged resident cost | **PARTIAL / BLOCKED** | Admission implementation exists; real native dynamic matrix and cost evidence absent. |
| Phase 7 no source rewrite, kernel hash behavior, one-binary/dynload qualification | **PARTIAL / BLOCKED** | Structural policy/mutations exist; native matrix rows absent. |
| Phase 8 deterministic range lock/update and fail-closed replacement | **PARTIAL / BLOCKED** | Source/spec/manual exist; production root-CLI system evidence is not current and phase ordering is unsatisfied. |

### KPF Follow-Through Relevant to Plan B

The newer KPF work materially advances the migration but does not replace the
original phase gates:

- Four-language generation, stable C ABI, native and worker transports,
  signature/trust admission, bounded no-GC runtime, strict allocation
  interposition, atomic rollback, lifecycle race tests, backend worker parity,
  semantic Simple check, Rust/C++ lint workers, tooling protocols, VS Code and
  SVIM cutovers, WIT generation, and an MDSOC++ pilot are present.
- Focused evidence includes Simple specs, native harnesses, Rust/C/C++ builds,
  and mutation-red checks reported by their owning commits.
- The current KPF performance normal gate is **not reproducibly passing** at
  this HEAD because faster table timing underflows unsigned overhead
  subtraction; mutation mode still passes.
- The original compiler closure checker currently fails, so broad KPF progress
  cannot establish plan-B completion.

### Plan B Verdict

Phases 0 and 5 have current contradictory evidence and are **MISSING/failing**.
Phases 1–4 and 6–8 are partial or blocked at required runtime/bootstrap/native
scope. Plan B remains **NOT COMPLETE**.

## Top Remaining Actionable Gaps

### Repository-Actionable

1. Remove or formally reclassify all 33 forbidden compiler/K0/K1-to-plugin
   imports, then rerun the closure and full phase evidence matrix.
2. Fix signed/unsigned overhead calculation in
   `scripts/check/kernel-plugin-fabric/benchmark-performance-capacity.shs` so a
   faster indirect path reports zero/negative overhead safely instead of a
   64-bit wraparound failure; rerun normal and mutation gates.
3. Complete one genuine producer-created Stage2→Stage3 chain on arm64 and retain
   immutable admission, compatibility, no-op/edit, tooling, and performance
   receipts; do not substitute the standalone release binary.
4. Execute the original phase 1–8 SPipe/bootstrap/native matrices with the
   admitted self-hosted runtime, including backend plugin-edit cache isolation,
   APK/SFFI native negotiation, Phase7 one-binary/dynload parity, and root CLI
   package-range behavior.
5. Produce admitted M4 evidence for every required edit/corruption/interruption
   fixture and an admitted long-lived 20-request RSS baseline.

### External/Environment Blockers

1. No admitted x86_64 Apple runner artifact/receipt exists; Intel-native M0–M4
   and universal two-slice qualification require an x86_64 macOS execution
   environment.
2. Distribution signing identity, notarization credentials/service, and release
   promotion authority are unavailable; M5 release cannot be proved locally.
3. The canonical checkout lacks a trustworthy admitted self-hosted
   `bin/release/simple` command surface for several phase/SPipe commands; the
   bootstrap producer chain must create it rather than using the Rust seed.

## Independent Conclusion

**STATUS: FAIL / NOT COMPLETE.** This is a completion audit result, not an
implementation failure claim for every partial component. The repository has
substantial correct implementation, but current authoritative evidence both
omits required native/cross-host rows and directly contradicts closure and KPF
performance pass claims. Neither source plan may be marked complete, merged as
fully qualified, or released from this HEAD.
