<!-- codex-architecture -->
# macOS Bootstrap and Reverse-Reference Harmonization Plan

**Date:** 2026-08-30

**Status:** Proposed; implementation claims below are audit results, not completion claims

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

This plan does not claim that cross-phase CAS promotion, complete semantic
reverse registries, kernel/plugin extraction, or universal bootstrap already
exists.

## 2. Audited implementation status

| Merged phase | Current authoritative substrate | Status and gap |
|---|---|---|
| P0 evidence | Native build reports compiled/cached/failed counts; bootstrap records command, source, provider, phase-profile, memory, and admission evidence. | **Partial.** Stable receipts exist, but cache-explain and macOS cold/warm/edit attribution are not one canonical report. |
| P1 indexed discovery | `aop_index/reverse_index.spl` stores selector/field/target/advice tables; linker `SymbolGraph.reverse_refs` and module-local `BlockDepGraph` exist. | **Partial, narrow.** These are not one persisted root/layer/feature registry. AOP read sets use conservative predicate-text inspection. Trait, generic, export, runtime-provider, initializer, and unresolved-call registries are incomplete. |
| P2 semantic queries | Frontend parse and HIR caches persist; dependency interface folds and source fingerprints fail closed. | **Partial.** No complete persistent query database, generation root, used-entry receipts, or red/green propagation across all semantic families. |
| P3 module artifacts | Native object roots are stable; full source fingerprints gate the changed module; interface surfaces and native module capsule witnesses can preserve sibling objects. | **Partial.** Signature/use/layout edits remain closure-coarse and final-link input receipts are incomplete. Compiler executable/source identity intentionally invalidates objects after compiler changes. |
| P4 shared bootstrap cache | Stage 2 and Stage 3 retain separate persistent native caches with lane ownership and TTL pruning. | **Not implemented as shared CAS.** There is no atomic cross-process result publication, conflict detection, pinned generation, crash recovery, lease-aware GC, or automatic Phase2→3 promotion. |
| P5 kernel/plugin split | Provider receipt identity is represented in native cache scope; runtime/provider admission scripts exist. | **Planned.** Bootstrap still compiles the compiler closure and optional product boundaries are not a unified versioned plugin registry. |

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

- Compose only admitted thin Phase3 candidates.
- Validate both slices and run the universal candidate natively on both runners.
- Sign/notarize only after verification; promotion changes an immutable pointer
  and does not rebuild.

## 7. Acceptance gates

| Gate | Required result |
|---|---|
| Source/provenance | Clean immutable source revision; exact compiler, provider, SDK, target, and command hashes. |
| Phase2 | Native executable starts, reports expected version, compiles a focused file, and passes bootstrap receiver/provider contracts. |
| Phase3 | Produced by admitted Phase2, starts natively, has stable source/provider lineage, and passes the same focused contracts. |
| Incremental no-op | Zero parsed/lowered/emitted modules where producer-neutral caches apply; zero link when ordered link inputs are unchanged. Until implemented, mark RED rather than relaxing it. |
| Private-body edit | Rebuild edited module and proven MIR/codegen consumers only; clean/incremental artifacts and diagnostics normalize equal. |
| Interface edit | Invalidate exact reverse dependents; unknown registry state triggers attributed conservative rebuild. |
| Cross-phase reuse | Every hit has an exact compatibility receipt; wrong producer/provider/target/schema is rejected. |
| Concurrency | No shared writable cache until atomic P4 publication exists; later tests cover identical/conflicting writers, pinned readers, crash recovery, and GC. |
| Memory/performance | Record wall, CPU, peak RSS, retained RSS, cache counts, and critical path; no monotonic retained growth across 20 warm requests. |
| Mach-O | Correct thin architecture and load commands; no ELF/PE object or linker flag; universal contains exactly the two admitted slices. |
| Tools | Phase2 and Phase3 full CLI/test runner build in producer-bound caches; MCP/LSP startup and one request pass. |
| Release | No stubs/fallback, no Rust-seed artifact substitution, native per-arch tests green, universal promoted without rebuild. |

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

- `doc/03_plan/compiler/bootstrap/stage3_native_cache_incrementality_2026-08-07.md`
- `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`
- `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`
- `doc/04_architecture/compiler/perf/simple_optimization_plugin.md`
- `scripts/bootstrap/bootstrap-from-scratch.sh`
- `.github/workflows/rust-bootstrap-multiplatform.yml`

The merged source plan and its TLDR are intentionally not linked as current-tree
paths until commit `7d4aac717e5` or an independently reviewed successor is
integrated.
