<!-- codex-architecture -->
# macOS Bootstrap and Reverse-Reference Harmonization Plan

**Date:** 2026-08-30

**Status:** Active implementation; **NOT COMPLETE**. Structural and portable
checks are recorded separately from SPipe, native, cross-host, and release
qualification. No unavailable row is treated as `PASS`.

**Independent M0–M5 re-audit (2026-09-03):**
`doc/09_report/compiler/macos_bootstrap_reverse_reference_m0_m5_independent_audit_2026-09-03.md`
records the current requirement-by-requirement result, centralized-storage
repairs, exact unavailable authority, and next-command prerequisites.

**Documentation reconciliation (2026-09-02):** Final requirements are recorded in
`doc/02_requirements/feature/macos_bootstrap_reverse_reference_harmonization.md`
and `doc/02_requirements/nfr/macos_bootstrap_reverse_reference_harmonization.md`.
SPipe planning is in
`doc/03_plan/sys_test/macos_bootstrap_reverse_reference_harmonization.md`.
`ReverseReferenceKeyV1`, the ten-family receipt path, and exact M2-to-M3
admission are now structurally implemented and independently audited. The
current admitted self-hosted binary still lacks the required `test`/`check`
surface, the latest isolated Stage3 build terminated with worker exit code 1
without a candidate or provenance receipt, and no native Intel evidence exists.
Therefore structural results do not establish runtime or native completion.
The Stage3 recovery authority guard now passes parent-sanity key normalization
but fails closed at `stage2-transcript-environment-set-mismatch`; no retry is
authorized until that binding is corrected and one complete 15-field authority
receipt passes.

**Cross-plan selected authority:** 1A LLVM+Cranelift K1, 2B ABI v1 now, 3A
`simple.sdn`, 4A atomic APK-only coverage, and baseline-relative 10% RSS
limits. For each architecture, maximum steady RSS is `<=110%` of its admitted
baseline and maximum growth across 20 requests is `<=10%` of baseline RSS.
Missing or architecture-mismatched baseline evidence fails closed.
The baseline authority validator is `WARN`: schema and workflow ordering are
implemented, but its one mutation run exposed a case-sensitive document check.
That check is corrected but not rerun, and real arm64/x86_64 baseline/sample
receipts remain absent.

**2026-09-03 independent HEAD audit:** the portable
`MacosBootstrapReceiptV1` schema and mutation-sensitive admission tests now
exist. Collector integration and native M0/M4/M5 evidence remain incomplete;
see `doc/09_report/compiler/macos_bootstrap_plan_independent_head_audit_2026-09-03.md`.

**Source plan:** `simple_compiler_performance_kernel_plugin_merged_plan_2026-08-30.md`
exists on unintegrated commit `7d4aac717e5`; this plan audits that immutable
version against authoritative source revision `92d86bac0c8`.

## 1. Outcome

Build and admit native pure-Simple Phase 2 and Phase 3 compilers on both
`aarch64-apple-darwin` and `x86_64-apple-darwin`, using the same conservative
reverse-reference and per-module witness model. An unchanged Phase 3 build
must reuse every artifact whose producer-neutral semantic and target-specific
codegen identities match. A universal binary is an optional packaging product
assembled only from two separately admitted architecture slices.

This plan does not claim native cross-phase qualification, a shared writable
CAS, a signed/notarized universal release, or completion of either target plan.

## 2. Audited implementation status

Status vocabulary:

- **STRUCTURAL PASS**: production source, wiring, and mutation/portable checks
  satisfy the inspected contract; this is not a runtime claim.
- **RUNTIME BLOCKED**: the required admitted self-hosted `simple` command could
  not execute the SPipe/product path.
- **NATIVE BLOCKED**: one or both required native macOS rows are absent.

| Milestone | Current determination | Authoritative source/test/report evidence |
|---|---|---|
| **M0 — baselines and receipts** | **PORTABLE/STATIC PASS; RUNTIME/NATIVE BLOCKED.** Receipt framing and live-byte admission are repaired. No current native arm64+Intel cold Phase2/3 baseline pair exists; the latest Stage3 attempt produced no candidate. | `scripts/check/check-macos-bootstrap-receipt.shs`; `test/01_unit/app/build/macos_bootstrap_receipt_spec.spl`; `doc/06_spec/03_system/app/compiler/feature/macos_bootstrap_receipt_m0_m1_evidence.md`; `build/review/m0_m1_receipt_adversarial_audit.md`; `build/review/self_hosted_runtime_recovery.md` |
| **M1 — target/linker correctness** | **PORTABLE/STATIC PASS; NATIVE BLOCKED.** Target, SDK, deployment, linker policy, provider bytes, archive members, and tool identity are bound and revalidated. No retained native arm64+x86_64 proof exists. | `src/app/build/targets/action_identity.spl`; `src/compiler/00.common/cache/darwin_runtime_provider_manifest.spl`; `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`; `test/02_integration/app/macos_native_action_identity_production_spec.spl`; `build/review/m0_m1_receipt_adversarial_audit.md` |
| **M2 — projection receipts** | **STRUCTURAL PASS; SPipe/NATIVE BLOCKED.** Ten typed registry families, private-body interface cutoff, ordinary-import/SCC separation, exact exported-interface consumers, lifecycle isolation, transitive/SCC closure, fail-closed fallback, and immutable receipts are present. The combined mutation matrix rejects 16/16 weakenings; no native incremental run is claimed. | `src/compiler/00.common/cache/reverse_reference_facts.spl`; `src/compiler/80.driver/cache/reverse_reference_receipt.spl`; `src/compiler/80.driver/driver_build/incremental.spl`; `test/02_integration/compiler/cache/reverse_reference_projection_receipt_spec.spl`; `scripts/check/check-m3-phase2-phase3-mutations.shs`; `doc/09_report/compiler/macos_m2_m3_incremental_reuse_2026-09-03.md` |
| **M3 — Phase2→3 compatible reuse** | **STRUCTURAL PASS; SPipe/NATIVE BLOCKED.** Exact immutable M2 receipt digest, owner/root generations, key frame, consumer, canonical no-follow reads, exclusive publication, attributed per-item decisions, and hit/rejection ledger summaries are enforced. No admitted native Phase2→3 reuse receipt or clean/reused output comparison exists. | `src/compiler/00.common/cache/phase_compatibility_manifest.spl`; `src/compiler/80.driver/cache/phase_compatibility_admission.spl`; `src/compiler/80.driver/driver_aot_native_output.spl`; `test/02_integration/compiler/cache/phase2_phase3_compatibility_manifest_spec.spl`; `doc/06_spec/03_system/compiler/macos_phase2_phase3_compatibility_spec.md`; `doc/09_report/compiler/macos_m2_m3_incremental_reuse_2026-09-03.md` |
| **M4 — native per-architecture qualification** | **PORTABLE CONTRACT PASS; NATIVE BLOCKED.** The exact eight fixtures, real work traces, live provider/archive mutation, producer-built tools, strict `Results:` parsing, and evidence manifests are structurally enforced. Neither architecture has a retained native PASS receipt. | `scripts/check/check-macos-reverse-reference-m4.shs`; `test/01_unit/scripts/macos_reverse_reference_m4_contract_test.shs`; `test/03_system/app/compiler/feature/macos_reverse_reference_m4_native_qualification_spec.spl`; `doc/06_spec/03_system/app/compiler/feature/macos_reverse_reference_m4_native_qualification_spec.md`; `build/review/independent_m4_reverse_reference_audit.md` |
| **M5 — universal packaging and promotion** | **PORTABLE STRUCTURAL PASS; NATIVE/RELEASE BLOCKED.** The immutable-snapshot wrapper rejected 5/5 mutations, excluded undeclared files, and then completed one drift-free portable qualification from an exact three-file inventory. Independent review confirmed normalized snapshot-root execution, digest-bound evidence, and read-only sealing. No admitted native slice pair or real Apple signing/notary evidence exists. | `scripts/check/check-macos-universal-m5-hermetic.shs`; `test/01_unit/scripts/macos_m5_hermetic_snapshot_wrapper_test.shs`; `scripts/release/macos-universal-m5.shs`; `test/03_system/app/compiler/feature/macos_m5_hermetic_portable_qualification_spec.spl`; `build/review/m5-portable-hermetic-20260902T082331Z-54605/status.env`; `build/review/independent_m5_hermetic_portable_qualification_audit_2026-09-02.md` |

Reverse-reference structures must remain distinct until their identities are
harmonized:

- semantic invalidation: declaration/query IDs and projection digests;
- native invalidation: module/SCC witness and object/action digest;
- linker reachability: emitted symbol IDs and relocation references;
- AOP invalidation: selector, descriptor-field, advice, and target IDs;
- bootstrap admission: producer, provider, target, source, and command digest.

A common frame may encode these keys, but one registry must not silently answer
another registry's question.

## 3. macOS target and artifact model

The two execution targets are independent:

```text
aarch64-apple-darwin  -> phase2/aarch64/simple -> phase3/aarch64/simple
x86_64-apple-darwin   -> phase2/x86_64/simple  -> phase3/x86_64/simple
```

Each Phase 2 compiler must execute natively on its build runner before it may
produce Phase 3. Rosetta is diagnostic convenience, never admission evidence.
The existing `macos-latest` and Intel runner entries are retained while the
Intel hosted runner exists. The workflow must record `uname -m`, compiler
Mach-O architecture, deployment target, SDK identity, Xcode/clang versions,
provider archive members, and binary SHA-256.

An optional universal artifact is produced after both thin Phase 3 artifacts
are independently green:

1. verify matching Simple version, source revision, compiler schema, public
   plugin/kernel ABI, runtime bundle, capabilities, and deployment policy;
2. run `lipo -create` into a new immutable candidate;
3. verify `lipo -info`, `file`, Mach-O load commands, signatures, and per-slice
   hashes recorded in its receipt;
4. run native startup/tests on both architectures from the universal candidate;
5. promote the already-tested digest without rebuilding either slice.

No x86_64 object, archive, or native cache entry is reused as an aarch64 object.
Only producer-neutral parse/HIR/query values may be shared when their schema
and semantic projections are exactly target-independent.

## 4. Cache layout and keys

Use isolated mutable indexes and immutable candidate artifacts:

```text
build/bootstrap/macos/<source-revision>/
  cache/<target>/phase2/<producer-sha>/<entry-closure>/
  cache/<target>/phase3/<producer-sha>/<entry-closure>/
  admission/<target>/<phase>/<candidate-sha>/receipt.env
  artifacts/<target>/<phase>/simple
  universal/<candidate-sha>/simple
```

Until P4 exists, Phase 2 and Phase 3 caches remain separately writable. Reuse
is explicit and read-only: compare the candidate module witness/action key,
then hard-link or copy an immutable object into the consuming lane only after
digest verification. Never point two compiler processes at one current mutable
`build_cache.sdn`.

Every reusable key binds:

- normalized source/query projection and dependency interface digests;
- compiler executable and compiler-source identity unless the artifact schema
  is explicitly producer-neutral;
- runtime/provider receipt and runtime bundle;
- target triple, CPU/features, deployment target, backend, optimization,
  object format, linker policy, and relevant SDK ABI;
- HIR/MIR/object/cache schema versions and entry-closure identity.

Absolute worktree paths, timestamps, log paths, phase labels, and runner names
must not affect a semantically portable content key. They remain receipt facts.

## 5. Reverse-reference harmonization

Introduce a versioned `ReverseReferenceKeyV1` contract in the compiler common
cache layer only after tests prove stable framing. Required fields are registry
kind, owner/root generation, subject identity, projection kind, projection
digest, and schema version. Registry-specific values stay in their current
owners; a common contract provides framing and validation, not a global mutable
singleton.

Required published projections are:

1. direct import and exported-name used-entry receipts;
2. trait/type implementation and method-candidate consumers;
3. unresolved method leaf/call-site candidates;
4. annotation consumers;
5. generic definition/specialization consumers;
6. AOP selector/read-field/advice/target consumers;
7. runtime operation/provider consumers;
8. initializer DAG dependents;
9. module/SCC MIR and object consumers;
10. emitted-symbol relocation consumers.

Missing generations or unknown change kinds fail closed to the existing
closure-wide rebuild and emit a measured fallback reason. A fallback cannot
satisfy a warm incremental performance gate.

## 6. Implementation sequence

### M0 — Freeze baselines and receipts

- Run current canonical `bootstrap-from-scratch.sh` on native Apple Silicon and
  Intel runners with no deployment.
- Record cold Phase2/3 wall time, peak/retained RSS, compiled/cached/failed,
  source reads, and artifact/import metadata.
- Add a macOS receipt validator and preserve the exact producer/provider hashes.

### M1 — Target-key and linker correctness

- Make Darwin target/deployment/SDK identity explicit in native action keys.
- Prove Darwin receives `-dead_strip` but no ELF hardening flags.
- Prove runtime/provider archives are Mach-O and match the requested slice.
- Add negative tests for architecture, SDK, provider, and deployment mismatch.

### M2 — Reverse-reference projection receipts

- Add the common framed key and immutable generation receipt.
- Persist the direct-import/export and module/SCC projections first.
- Adapt AOP reverse indexes without weakening their conservative fallback.
- Add trait/generic/runtime/initializer families only with causal positive,
  negative, boundary, and corruption tests.

### M3 — Phase2→3 compatible reuse

- Keep Phase2 and Phase3 writable caches separate.
- Produce a read-only compatibility manifest from Phase2.
- Let Phase3 admit producer-neutral frontend values and exact compatible native
  objects; report a reason for every reused or rejected item.
- Compare normalized clean and reused outputs byte-for-byte or by documented
  nondeterministic-field normalization.

### M4 — Native per-architecture qualification

- Build, start, and run focused compiler, full-CLI, test-runner, MCP, and LSP
  smokes on each architecture.
- Run no-op, private-body, exported-interface, provider, linker-policy, corrupt
  cache, interrupted build, and one-file edit fixtures.
- Require a real test `Results:` line; exit 0 without results is not evidence.

### M5 — Universal packaging and promotion

- Run focused portable qualification only through
  `scripts/check/check-macos-universal-m5-hermetic.shs`; bind the exact source
  inventory and reject source or snapshot drift before accepting its evidence.
- Compose only admitted thin Phase3 candidates.
- Validate both slices and run the universal candidate natively on both runners.
- Sign/notarize only after verification; promotion changes an immutable pointer
  and does not rebuild.

## 7. Acceptance gates

| Gate | Required result | Current audited status |
|---|---|---|
| Source/provenance | Clean immutable source revision; exact compiler, provider, SDK, target, and command hashes. | **BLOCKED:** shared worktree is dirty and no final immutable native receipt pair exists. |
| Phase2 | Native executable starts, reports expected version, compiles a focused file, and passes bootstrap receiver/provider contracts. | **NATIVE BLOCKED:** no current arm64+x86_64 admitted pair. |
| Phase3 | Produced by admitted Phase2, starts natively, has stable source/provider lineage, and passes the same focused contracts. | **RUNTIME/NATIVE BLOCKED:** latest Stage3 worker exited 1 without candidate/provenance. |
| Incremental no-op | Zero parsed/lowered/emitted modules where producer-neutral caches apply; zero link when ordered link inputs are unchanged. Until implemented, mark RED rather than relaxing it. | **RED / NOT PROVEN:** no retained native production receipt. |
| Private-body edit | Rebuild edited module and proven MIR/codegen consumers only; clean/incremental artifacts and diagnostics normalize equal. | **STRUCTURAL; NATIVE BLOCKED.** |
| Interface edit | Invalidate exact reverse dependents; unknown registry state triggers attributed conservative rebuild. | **STRUCTURAL PASS; NATIVE BLOCKED.** |
| Cross-phase reuse | Every hit has an exact compatibility receipt; wrong producer/provider/target/schema is rejected. | **STRUCTURAL PASS; RUNTIME/NATIVE BLOCKED.** |
| Concurrency | No shared writable cache until atomic P4 publication exists; later tests cover identical/conflicting writers, pinned readers, crash recovery, and GC. | **SOURCE COMPLETE / NATIVE PROCESS MATRIX PENDING:** P4 uses exclusive no-follow immutable generation files, fsync-before-rename pointer publication, generation leases, dead-owner recovery, and bounded deterministic GC. Identical retries are idempotent; conflicting parents fail closed. Interpreter acceptance is 9/9 with 5 mutation classes; existing native thread/process fixtures cover conflicting writers, pinned readers, GC, and dead-process lease recovery. A new all-process identical/conflicting writer fixture remains pending because the admitted compiler rejected its source during discovery. |
| Memory/performance | Record wall, CPU, peak RSS, retained RSS, cache counts, critical path, and request latency. Require an admitted architecture-matched baseline; maximum steady RSS must be `<=110%` of baseline and maximum growth across 20 requests must be `<=10%` of baseline RSS. | **BLOCKED:** no qualifying admitted native baseline/measurement pair exists. Missing baseline fails closed; no numeric value selection remains pending. |
| Mach-O | Correct thin architecture and load commands; no ELF/PE object or linker flag; universal contains exactly the two admitted slices. | **STRUCTURAL; NATIVE BLOCKED.** |
| Tools | Phase2 and Phase3 full CLI/test runner build in producer-bound caches; MCP/LSP startup and one request pass. | **NATIVE BLOCKED:** M4 has no native PASS row. |
| Release | No stubs/fallback, no Rust-seed artifact substitution, native per-arch tests green, universal promoted without rebuild. | **BLOCKED / NOT READY.** |

## 8. Sidecar and merge ownership

Sidecar lanes are **N/A until scheduled**. When scheduled, recommended
independent lanes are:

- Apple Silicon bootstrap/evidence;
- Intel bootstrap/evidence;
- reverse-reference key/projection implementation;
- Phase2→3 compatibility manifest and cache adversarial tests;
- universal packaging/signing checks.

Before sidecars start, the merge owner defines the exact
`ReverseReferenceKeyV1`, `MacosBootstrapReceiptV1`, compatibility-manifest
fields, fixture names, and fail-closed assertions. Sidecars must not invent
parallel schemas.

**Merge owner:** compiler bootstrap/cache integration owner.

**Final reviewer:** independent normal/highest-capability reviewer who did not
implement any lane. The reviewer checks both architectures and rejects broad
done marks based only on source assertions or Rust seed artifacts.

## 9. Documentation links

- `doc/03_plan/compiler/perf/persistent_package_module_index_compile_optimization_plan_2026-09-02.md`
- `doc/03_plan/compiler/bootstrap/stage3_native_cache_incrementality_2026-08-07.md`
- `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`
- `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
- `doc/04_architecture/compiler/perf/simple_optimization_plugin.md`
- `scripts/bootstrap/bootstrap-from-scratch.sh`
- `.github/workflows/rust-bootstrap-multiplatform.yml`

The merged source plan and its TLDR are intentionally not linked as current-tree
paths until commit `7d4aac717e5` or an independently reviewed successor is
integrated.
