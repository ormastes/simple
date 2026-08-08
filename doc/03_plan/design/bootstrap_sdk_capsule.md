<!-- codex-architecture -->
# Future Plan: Provenance-Bound Bootstrap SDK Capsule

Status: planned after the current x86 Stage 4 bootstrap is admitted

## Toolchain prerequisite

The first capsule authority must bind a Clang/LLVM 23.1 toolchain identity.
Its manifest records the exact `llvm-config`, `clang`, `llvm-as`, `opt`, and
`llc` versions and hashes. LLVM 18/20 artifacts are incompatible historical
diagnostics, not a valid capsule seed. The Rust seed's Inkwell/llvm-sys
binding must migrate before this prerequisite can be met.

Current staging evidence is deliberately weaker: a local LLVM 23.1.0-rc2
provider can expose all five tools and headers, and `aya-llvm-sys 231` links
against it under strict versioning. It is disposable host evidence only until
the provider is pinned into the capsule and Inkwell exposes a reviewed
`llvm23-1` feature.

## Goal

Adopt a Clang-style two-generation bootstrap boundary: build a new compiler
against a frozen, verified SDK capsule; use that compiler to rebuild both the
SDK and compiler; verify reproducibility; then promote the compiler and SDK as
one rollback-safe unit.

This is a correctness and build-graph boundary, not a way to hide self-hosting
errors. `src/compiler/**` must still rebuild from source. Stable library and
runtime dependencies may be consumed from the capsule only when their complete
typed interfaces, required bodies, ABI, options, and dependency hashes match.

## Current Gap

- `core-c-bootstrap` supplies a runtime link bundle, not a compiler-facing SDK.
- SHB/SMF already provide interface and dependency-hash machinery, but the SHB
  surface is not complete enough to be bootstrap authority. In particular,
  enum entries retain variant names without the payload type closure that the
  Stage 4 `MirInstKind` failure required.
- Stage 4 therefore reparses and retains the broad source closure and discovers
  dependent HIR defects sequentially.
- AOP/MDSOC, comptime, generics, layouts, resolver behavior, compiler ABI, or
  target changes still require broad invalidation.

## Frozen Interface Names

- `BootstrapSdkManifest`: version, target, compiler/runtime ABI, options,
  source revision, complete artifact inventory, hashes, and signature.
- `BootstrapSdkModuleInterface`: complete typed public and required-private
  closure derived from SHB, with terminal declaration provenance.
- `BootstrapSdkBodyArchive`: bodies required by generics, comptime, inlining,
  AOP/MDSOC weaving, reflection, and monomorphization.
- `BootstrapSdkProvenance`: stage compiler identity, runtime bundle identity,
  toolchain/sysroot identity, dependency graph root, and admission evidence.

These names are shared contracts owned under `src/compiler/00.common` or the
nearest existing common driver contract; loader, driver, compiler, and tooling
consume them without reaching into sibling-private implementations.

## Promotion Flow

1. Select the last admitted compiler plus `bootstrap-sdk-vN` as immutable
   Stage 0 authority.
2. Build the candidate compiler from source against `bootstrap-sdk-vN`.
3. Use the candidate to rebuild all SDK interfaces, required bodies, runtime
   objects, and target metadata as `bootstrap-sdk-vN+1`.
4. Rebuild the compiler against `bootstrap-sdk-vN+1`.
5. Rebuild once more when reproducibility proof is requested; compare semantic
   manifests and normalized binaries, not timestamps or filesystem paths.
6. Run exact compiler, test-runner, lint, duplicate-check, provenance, and
   corruption/fallback gates.
7. Atomically promote compiler + SDK manifest + artifacts. Retain the previous
   admitted pair until post-swap sanity passes; restore both on failure.

## Phased Work

### P0 — Complete the interface authority

- Extend SHB types, extraction, hashing, reading, and validation for enum
  payloads, generic parameters/bounds/defaults, aliases, traits, associated
  items, layouts, visibility, re-export terminal origins, effects, and calling
  conventions.
- Record dependency closure separately from lexical import spelling.
- Define which generic/comptime/AOP bodies are mandatory in the body archive.
- Fail closed on any unsupported declaration rather than omitting it.

### P1 — Capsule writer, reader, and admission

- Emit the four frozen contracts deterministically from an admitted compiler.
- Bind every file by path, size, digest, target, backend, options, compiler ABI,
  runtime ABI, and direct dependency-interface hashes.
- Verify the complete manifest before any module is loaded. No partial capsule,
  seed identity, missing body, stale interface, or unsigned substitution may
  fall back to source or stubs silently.

### P2 — Opt-in driver consumption

- Add an explicit bootstrap-SDK input to the pure-Simple driver.
- Resolve capsule interfaces through the canonical module resolver and preserve
  physical terminal identities across aliases and re-exports.
- Compile changed compiler modules from source while loading admitted stable
  library modules from the capsule.
- Retain a diagnostic mode that compares capsule and from-source interfaces.

### P3 — Two-generation bootstrap and atomic promotion

- Teach `bootstrap-from-scratch.sh` to build candidate compiler, rebuilt SDK,
  second-generation compiler, reproducibility evidence, and rollback bundle.
- Keep `--fresh-cache` and clean-release proof. Incremental mode may reuse only
  artifacts whose full action/dependency keys match.
- Never deploy compiler and SDK independently.

### P4 — Performance and inventory evidence

- Report modules sourced, loaded from SDK, invalidated, rebuilt, failed, cached,
  and remaining for every layer.
- Measure cold/warm wall time, per-phase CPU utilization, max RSS, interface
  loading time, and cache validation time against the current full-source Stage
  4 baseline.
- Preserve fail-fast authoritative bootstrap plus collect-all independent-file
  diagnostics; do not treat cascaded post-corruption errors as independent.

### P5 — Platform capsules

- Produce target-specific SDKs for Linux x86_64/AArch64, macOS, Windows,
  FreeBSD, SimpleOS x86_64/AArch64, and supported RISC-V object lanes.
- Share target-independent interfaces only when ABI/layout hashes prove them
  identical. Runtime objects, sysroots, calling conventions, and layouts remain
  target-specific.

## Acceptance Criteria

- `SDK-001`: every supported public type form round-trips with an identical
  interface hash, including enum payload closure and generic bounds/defaults.
- `SDK-002`: aliases and re-exports preserve physical `(module,item,kind)`
  identity; same-terminal aliases pass and different-terminal collisions fail.
- `SDK-003`: required generic/comptime/AOP bodies are present and independently
  hashed; deleting or substituting one fails before compilation.
- `SDK-004`: source, compiler ABI, runtime ABI, target, backend, options, or
  dependency-interface changes invalidate exactly the proven affected closure.
- `SDK-005`: corrupt, truncated, mixed-version, wrong-target, Rust-seed, or
  stub-bearing capsules fail closed with no fallback artifact.
- `SDK-006`: candidate compiler rebuilds the SDK and then rebuilds itself using
  only the admitted previous pair plus declared host tools.
- `SDK-007`: normalized second/third-generation manifests are reproducible;
  unexplained differences block promotion.
- `SDK-008`: compiler + SDK deploy and rollback atomically, with exact-binary
  sanity and essential-tools markers before old artifacts are removed.
- `SDK-009`: full-source comparison mode proves capsule and source interfaces
  equal across the compiler/lib closure.
- `SDK-010`: cold/warm time, CPU, RSS, cache, module/file/task progress, and
  remaining-time evidence are retained without changing semantics.

## Explicit Exclusions

- Do not freeze compiler implementation modules to make self-hosting green.
- Do not accept shallow symbol-name-only interfaces.
- Do not let entry-closure text scanning become dependency authority.
- Do not use the Rust seed as production compiler or test evidence.
- Do not weaken HIR/MIR/LLVM validation, generate stubs, or continue from a
  corrupted shared compiler state merely to enumerate cascade diagnostics.

## Test and Review Ownership

- Sidecar lanes: interface/schema matrix; provenance/corruption; incremental
  invalidation; platform capsule matrix; performance/progress evidence.
- Merge owner: primary Stage 4/SPipe Codex lane.
- Final reviewer: independent normal/highest-capability Codex after all
  executable gates, generated manuals, and exact-binary evidence are present.
- Planned executable flow labels: `step("admit frozen SDK")`,
  `step("build candidate compiler")`, `step("rebuild candidate SDK")`,
  `step("rebuild compiler against candidate SDK")`, and
  `step("promote or roll back compiler and SDK")`.

## Related Paths

- `doc/04_architecture/compiler/bootstrap_build_modes.md`
- `src/compiler/80.driver/shb/`
- `src/compiler/80.driver/smf_writer.spl`
- `src/compiler/80.driver/cache/`
- `src/compiler/99.loader/module_resolver/`
- `scripts/bootstrap/bootstrap-from-scratch.sh`
