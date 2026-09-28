# Runtime Optional Provider and Binary-Size Optimization Plan

## Goal

Preserve all Simple features and architectures while making optional libraries truly demand-loaded, preferring qualified pure-Simple implementations, matching Python's base interpreter loading footprint, and measuring release-small hello against C with the same required startup and link inputs.

## Phase 0 — Baselines and Attribution

- Add matched Simple/Python startup/RSS and Simple/C binary-size harnesses.
- Retain linker maps, removed sections, symbols, dependencies, constructors, unwind/RTTI inventory, and hashes.
- Reproduce historical sub-40 KB hello or record the exact blocker.

Gate: every retained byte and loaded library has an owner/reason.

## Phase 1 — Metadata-Only Provider Registry

- Separate provider descriptors from provider handles and initialization.
- Remove default autoload for optional file extensions, network, crypto, DB, compression, XML, TUI, UI, web, audio, and GPU libraries.
- Add single-flight demand admission and typed rejection.

Gate: no-import hello maps and initializes zero optional providers.

## Phase 2 — Pure-Simple Dual Providers

- Inventory pure-Simple and foreign equivalents.
- Normalize traits, results, and errors.
- Add stability receipts, safe shadow classification, cohort selection, and rollback.
- Promote pure-Simple providers individually; never bulk-switch by directory.

Gate: feature/error parity across every supported architecture; effectful operations execute once.

## Phase 3 — Exact Runtime and Link Closure

- Build `RuntimeFeatureClosureV1` before provider initialization.
- Split runtime objects into function/data sections and hide non-exported symbols.
- Reject undeclared constructors, exported roots, archive members, and dynamic dependencies.
- Apply section GC, as-needed, and admitted ICF.

Gate: NoGC hello links no collector/compiler/backend/optional-provider sections.

Implementation status (2026-09-02): BS1 is implemented in
`src/compiler/70.backend/linker/runtime_feature_closure.spl` and integrated at
the LLVM native link boundary. Demand-action and provider identities now own
exact retained roots and reasons; undeclared or unretained roots fail closed;
the closure digest is bound into entry/link receipts. Focused static and
mutation-red contracts pass. Executable Simple tests remain pending an admitted
full CLI with `test` support.

Current-branch correction (2026-09-28): the named
`runtime_feature_closure.spl` and `RuntimeFeatureClosureV1` do not exist in the
isolated Target 5/6 branch. The historical BS1 statement above is not an
implementation receipt for this branch. The actual pure-Simple linker has
`NativeLinkConfig.retained_symbols` and runtime-bundle selection, but no exact
closure type/manifest with the stated admission invariants. Phase 3 remains
open. A focused Stage2 entry-closure hello built and ran at 21,016 stripped
bytes on Linux aarch64, with only libc in `DT_NEEDED`; it is pre-Stage4 and
does not satisfy the release-small gate. See
`doc/09_report/compiler/target56_shb_visibility_and_hello_diagnostic_2026-09-28.md`.
The current full CLI closure now compiles all 2,488 source units after a
typed-row HIR fix, but Stage4 `host-gpu` linking still reports 173 distinct
undefined symbols, chiefly from optional Vulkan, Metal, SQLite, CUDA, SDL,
and ROCm paths. This is direct evidence that those paths still reach the core
link instead of an admitted first-demand provider. See
`doc/09_report/compiler/target56_stage4_cli_link_boundary_2026-09-28.md`.

## Phase 4 — No-Unwind/No-RTTI Release-Small

- Add `NoUnwindProofV1` and target-specific post-link scanners.
- Disable exceptions, unwind tables, and RTTI only under a complete proof.
- Rebuild foreign libraries without these features when safe; otherwise isolate them in demand-loaded provider artifacts.
- Keep debug and ordinary release behavior unchanged.

Gate: injected exception, unwind, RTTI, personality, or foreign-boundary requirement rejects release-small.

## Phase 5 — Size and Loading Gates

- Unstripped NoGC hello below 2 MiB on all native targets.
- Linux stripped release-small hello at most 15 KiB and at most 1.05x same-host, same-toolchain C with the same startup wrapper, required runtime archive, linker options, section GC, and strip policy.
- Other targets use same-host C plus an admitted format allowance.
- Minimal interpreter startup/RSS at most 110% of same-host Python baseline.
- Run 30-sample development and 100-sample release cohorts.

Gate: binary hashes, toolchains, checksums, p50/p95, RSS, and attribution evidence are complete.

Implementation status (2026-09-02): BS7 cohort production and checking are
implemented by `scripts/check/produce-runtime-binary-size-startup-cohort.shs`
and `scripts/check/check-runtime-binary-size-startup-cohort.shs`. The checker
recomputes p50/p95 startup and max RSS, enforces the declared matched-startup C size limit,
requires empty NoGC-forbidden and optional-provider traces, requires 30
development or 100 release samples per lane, and rejects Rust seed or
pre-Stage4 evidence. The focused mutation suite passes. No heavy cohort has
been run, so native development and release qualification remain pending.

## Phase 6 — Feature and Architecture Qualification

- Exercise every provider family on every supported architecture.
- Prove a feature excluded from hello remains available on first demand.
- Test missing, corrupt, incompatible, concurrent, and crashing providers.
- Prove loader and file-view changes do not alter user-visible semantics.

Gate: full feature matrix passes with no static optional dependency regression.

## Phase 7 — Cutover

- Make metadata-only registration and demand loading the default.
- Make qualified pure-Simple providers default individually.
- Keep explicit rollback for one release window.
- Remove legacy eager-autoload paths only after mutation-red evidence.

## Required SPipe Evidence

- System spec: provider declaration, demand load, rejection, concurrency, rollback, and feature preservation.
- Performance spec: Python-relative startup/RSS and C-relative binary size.
- Mutation suite: forced eager load, undeclared dependency, coarse section retention, collector root, unwind/RTTI injection, dual effect execution, and missing attribution.

## Completion Conditions

- No optional provider loads for no-import hello.
- Pure-Simple provider promotion is receipt-backed and reversible.
- No feature or architecture is removed.
- Unstripped and stripped size targets pass.
- Release-small contains no unjustified unwind/exception/RTTI machinery.
- Documentation, manifests, executable SPipe, and generated manuals agree.
