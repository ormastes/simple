# Agent Tasks — Interpreter Loader and Generated Binary Size Optimization

Date: 2026-09-02

## Scope and Authority

This plan consolidates the remaining work from:

- `doc/03_plan/agent_tasks/bootstrap_compiler_interpreter_loader_arch_refactor.md`
- `doc/09_report/compiler/interpreter_startup_tracking_cleanup_2026-08-22.md`
- `doc/03_plan/compiler/optimization/executable_size_reduction.md`
- `doc/03_plan/compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md`
- their requirements, architecture, detail-design, and executable-test artifacts.

The demand-driven SMF pipeline owns package discovery, SCV snapshots, package
images, pinned archive reads, import/HIR/MIR demand, action scheduling, shared
artifact-service profiles, file views, and backend promotion. This plan consumes
those APIs; it must not create competing cache, scheduler, archive, snapshot, or
file-view owners.

Vendored runtime code is excluded. Rust-seed implementation is historical or
bootstrap-only evidence and is not proof of the pure-Simple production path.

## Current Evidence

- The 2026-08-22 tracking cleanup removed the proven recursive startup scan:
  `getdents64` fell from 132 to zero and median startup from 50 ms to 20 ms.
  This is valid attribution evidence, but only for the measured Rust-seed and
  isolated candidate; it is not Stage4 release evidence.
- `scripts/check/produce-interpreter-startup-evidence.shs` and
  `scripts/check/check-interpreter-startup-parity.shs` provide retained,
  hash-bound cold/warm startup evidence. Native admitted results remain needed.
- Explicit native runtime roots, diagnostic whole-archive fallback, release
  stripping, size budgets, runtime ABI separation, and dependency-audit
  surfaces exist. Their broad behavior still requires current native evidence.
- Loader/SMF implementation exists under `src/compiler/99.loader/`, while the
  demand pipeline now owns typed package-image reads and pinned capabilities.
  Compatibility loader lifecycle must remain separate until a shared facade is
  proven; direct duplication of SMF parsing or file access is forbidden.
- Metadata-only optional-provider behavior has partial executable coverage,
  including zero-load startup policy. Complete runtime closure, no-unwind proof,
  exact attribution, architecture qualification, and release-small evidence are
  not yet proven.

## Requirement Matrix

### Bootstrap / Interpreter / Loader Refactor

| Requirement | Status | Evidence | Remaining work |
|---|---|---|---|
| Pure-Simple normal bootstrap; Rust only under full bootstrap | Partial | Bootstrap policy and scripts enforce the intended mode | Prove with admitted Stage4 bootstrap evidence |
| Numbered compiler layers use public facades | Partial | Numbered layer map and many boundary audits exist | Run focused layer-edge audit for interpreter/loader paths and remove remaining sibling-private imports |
| Interpreter and driver share resolver, diagnostics, session/cache identity | Partial | Shared compiler diagnostics and demand entry/package resolution exist | Introduce one interpreter-load facade that consumes demand-entry and immutable snapshot identities |
| Loader and driver share SMF metadata, symbol, relocation, and identity contracts | Partial | Package-image/pinned-capability work and loader SMF implementation exist | Define adapter facade; remove duplicate parser/file-open authority without merging lifecycle loaders |
| Interpreter execution state stays private | Partial | Interpreter code remains in interpreter-owned trees | Add boundary test proving no external mutation or private-subtree import |
| `dynload` default and `one-binary` conservative mode | Implemented, runtime pending | Existing bootstrap mode policy | Re-prove once with admitted full CLI |
| Startup tracking cleanup avoids recursive scans and cross-process temp deletion | Implemented, release pending | 2026-08-22 syscall and concurrency evidence | Reproduce on admitted Stage4 binary and current SCV/package-index path |

### Executable Size Reduction (`REQ-001..014`)

| Requirements | Status | Evidence | Remaining work |
|---|---|---|---|
| REQ-001..004 explicit roots and fallback | Implemented, native pending | Native linker has explicit root calculation and `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE` fallback | Native mutation and link-map proof on supported targets |
| REQ-005..006 strip and reusable budgets | Implemented, native pending | `scripts/check-executable-size-budgets.shs`; release/native-build strip paths | Produce current CLI/MCP/LSP/generated/runtime size receipts |
| REQ-007..010 loader ABI and dependency closure | Implemented structurally | `simple-runtime-abi`; native loader depends on it; audit surfaces exist | Run deterministic dependency audit and prove allowlists against current manifests |
| REQ-011..014 native dependency attribution and stale dependency removal | Partial | Native dependency audit contract/spec exists; known overreach is documented | Generate current reports and remove only evidenced startup-path overreach |
| NFR-001..008 deterministic fail-closed checks | Partial | Budget and dependency scripts support explicit missing-artifact policy | One admitted cross-platform evidence cohort remains required |

### Runtime Optional Providers and Release-Small (`REQ-001..015`)

| Requirements | Status | Evidence | Remaining work |
|---|---|---|---|
| REQ-001..002 metadata-only registration and first-demand admission | Partial | DynSMF demand-load policy and provider contracts exist | One shared provider state machine with ABI/digest/dependency/policy receipt and concurrency proof |
| REQ-003 exact entry closure | Partial | Demand package/index/action path exists | Bind `RuntimeFeatureClosureV1` to linker and loader receipts; reject undeclared roots |
| REQ-004..006 pure-Simple dual providers | Partial | Provider contracts and individual provider gates exist | Typed cohort/shadow/rollback authority and per-provider qualification matrix |
| REQ-007 NoGC exclusion | Missing proof | Runtime boundary audits exist | Prove zero collector sections, constructors, and initialization in no-allocation hello |
| REQ-008..010 no-unwind/no-RTTI profile | Missing | Design exists | Implement `NoUnwindProofV1`, target scanners, foreign-provider isolation, and profile-specific flags |
| REQ-011..012 feature preservation and typed absence | Partial | Provider-specific tests exist | Complete architecture/provider matrix, concurrent/crash rejection, and error parity |
| REQ-013..014 complete link attribution | Partial | Size/dependency scripts and linker information exist | Canonical receipt for modules, sections, constructors, exports, DSOs, maps, removed sections, hashes |
| REQ-015 sealed pure-Simple provider sections | Partial | Demand SMF/package archives exist | Bind provider publication/loading to package-image and pinned-capability APIs |
| NFR-001..003 binary-size targets | Unproven | Harness/checkers exist | Admitted same-toolchain C comparisons on every native target |
| NFR-004 Python-relative interpreter startup/RSS | Unproven for release | Producer/checker exists; old seed evidence is diagnostic only | 30-sample development and 100-sample release cohorts on admitted Stage4 |
| NFR-005..007 loading isolation and evidence quality | Partial | Zero-load and provider-specific checks exist | Complete dynamic-library/init counters, architecture matrix, hashes, p50/p95, RSS, checksums |

## Non-Overlapping Missing Lanes

Each lane has an exclusive production write set. Existing demand-pipeline files
are integration dependencies and may be changed only by its merge owner.

| Lane | Exclusive production write set | Deliverable / gate |
|---|---|---|
| IL1 INTERPRETER-LOAD-FACADE | `src/compiler/95.interp/load_facade/**` | Shared resolver/diagnostic/snapshot identities; no private loader imports or live-tree fallback |
| IL2 LOADER-SMF-ADAPTER | `src/compiler/99.loader/shared_contract/**` | Adapter from package image and pinned capability to loader symbols/relocations; no duplicate parser or reopen |
| IL3 LOADER-BOUNDARY-AUDIT | `scripts/audit/compiler-interpreter-loader-layering.shs` | Fail on sibling-private imports, duplicate SMF authority, or interpreter-state escape |
| BS1 RUNTIME-FEATURE-CLOSURE | `src/compiler/70.backend/linker/runtime_feature_closure.spl` | `RuntimeFeatureClosureV1`; exact retained roots/reasons; no provider initialization |
| BS2 PROVIDER-ADMISSION | `src/compiler/99.loader/provider_admission/**` | Metadata-only single-flight state machine, typed rejection, effect-once dual-mode policy |
| BS3 RELEASE-SMALL-PROOF | `src/compiler/70.backend/linker/no_unwind_proof.spl`; `scripts/check/check-release-small-unwind-rtti.shs` | Fail-closed exception/unwind/RTTI proof and target scanners |
| BS4 LINK-ATTRIBUTION | `scripts/check/produce-native-link-attribution.shs`; `scripts/check/check-native-link-attribution.shs` | Implemented structurally: hash-bound binary/action/runtime-closure receipt, canonical retained/removed section, symbol, DSO, constructor, export attribution, exact owner/reason ledger, and mutation-red unit gate. Admitted native evidence remains pending. |
| BS5 DEPENDENCY-TRIM | Rust manifests and source files explicitly named by the dependency audit only | Implemented conservatively: removed only the unused `simple-native-loader` dev `cc` crate; retained every owned-code/feature-graph dependency; receipt and fail-closed static check added |
| BS6 PROVIDER-MATRIX | `test/03_system/runtime/provider/**`; matching `doc/06_spec/03_system/runtime/provider/**` | Executable 20-row portable/family/architecture matrix added; portable metadata-only and isolation contracts execute now, while unavailable native/provider receipts remain explicitly pending. Covers feature/error parity, architecture coverage, absence/corruption/concurrency/crash/rollback, effect-once, and zero hidden provider load. |
| BS7 SIZE-COHORTS | `test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl`; `scripts/check/produce-runtime-binary-size-startup-cohort.shs`; `scripts/check/check-runtime-binary-size-startup-cohort.shs` | Implemented structurally: NoGC and zero-provider inventories must be empty; same-host C size and Python p50/p95 startup/RSS gates are recomputed; development requires 30 samples and release requires 100; only admitted pure-Simple Stage4 receipts qualify and seed evidence is rejected. Mutation checks pass; heavy admitted cohorts remain pending. |
| BV FINAL-REVIEW | `build/review/interpreter_loader_binary_size_optimization_audit.md` | Requirement-by-requirement PASS/FAIL; no production ownership |

## Reserved Active Owners

- Demand-driven SMF pipeline owns `src/app/compiler_entrypoint/**`,
  `src/compiler/80.driver/action_graph/**`, `src/compiler/80.driver/smf/**`,
  `src/compiler/20.hir/**`, `src/compiler/50.mir/admission/**`,
  `src/lib/compiler_artifact_service/**`, and common read-only file views.
- Persistent package-index/SCV lanes own package indexes, archive CAS batching,
  snapshots, event inventories, and host-shared cache lifecycle.
- Bootstrap harmonization owns Stage2/3/4 admission, deployment generations,
  macOS M4/M5 qualification, and release-slot mutation.
- These owners expose typed APIs to this plan. This plan must not fork, wrap
  around, or silently bypass their authority.

## Merge Order

1. IL3 records current boundary failures without production edits.
2. IL1 and IL2 land against frozen demand-pipeline interfaces.
3. BS1 and BS2 land independently, then the demand merge owner connects them.
4. BS3 and BS4 land before any size target can pass.
5. BS5 removes only attribution-proven dependencies.
6. BS6 runs feature/architecture qualification.
7. BS7 produces admitted development and release cohorts.
8. BV audits every requirement and freshness of generated manuals.

## Completion Rule

Completion requires executable SPipe evidence, current generated manuals, and
admitted native receipts for every requirement above. Structural checks, old
Rust-seed measurements, absent artifacts, or expected-red specs cannot establish
PASS. No feature or architecture may be removed to satisfy a size target.
