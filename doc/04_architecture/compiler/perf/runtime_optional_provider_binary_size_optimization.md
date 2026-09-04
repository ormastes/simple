# Runtime Optional Provider and Binary-Size Optimization Architecture

## Decision

Use a minimal base runtime plus sealed demand-loaded provider capsules. Provider registration is metadata-only. The linker consumes an exact reachability manifest, and the loader consumes a separate capability-admission manifest. Pure-Simple and foreign implementations coexist behind one typed provider slot until the pure-Simple implementation satisfies promotion gates.

## Layers

1. **Language closure layer** computes demanded symbols, initialization effects, runtime capabilities, diagnostics profile, target, and architecture.
2. **Provider policy layer** selects pure-Simple, foreign, dual-shadow, or unavailable without executing provider code.
3. **Artifact layer** resolves sealed SMF/native provider artifacts by content identity.
4. **Link layer** emits only base-runtime and statically demanded sections, with hidden visibility and fine-grained section GC.
5. **Loader layer** loads a provider capsule on first admitted capability demand and publishes it atomically to that slot.
6. **Evidence layer** records closure reasons, size attribution, loaded modules, startup/RSS, and parity.

Only adjacent layers communicate through typed values. Provider implementation code cannot alter closure or policy authority.

## Core Types

- `RuntimeFeatureClosureV1`: symbols, initialization effects, capabilities, diagnostics, architecture, and build profile.
- `ProviderDescriptorV1`: capability, ABI, target, digest, dependencies, side-effect class, and implementation kind.
- `ProviderStabilityReceiptV1`: correctness, mutation, performance, resource, architecture, and failure-parity evidence.
- `ProviderSelectionV1`: `PureSimple`, `Foreign`, `DualShadow`, or `Unavailable` plus rationale.
- `RuntimeLinkManifestV1`: exact sections, exports, constructors, dynamic dependencies, and retention reasons.
- `NoUnwindProofV1`: whole-closure proof that exception, unwind, stack-unwind, RTTI, and foreign-boundary requirements are absent.
- `BinarySizeReceiptV1`: toolchain, input manifests, map hashes, section/symbol totals, stripped/unstripped bytes, baseline, and verdict.

## Dynamic Loading State Machine

`Declared -> Admitting -> Loading -> Verifying -> Ready | Rejected`

Transitions are single-flight and generation-bound. Rejection is cached for the same artifact/policy generation. Loading never mutates Git, source, configuration, or unrelated provider slots.

## Dual-Provider Policy

- Default during stabilization: foreign provider executes; pure-Simple may shadow only pure bounded operations.
- Candidate phase: pure-Simple executes in selected cohorts; foreign provider remains explicit rollback.
- Promoted phase: pure-Simple is default; foreign provider is loaded only by policy or unsupported-capability demand.
- Retired phase: foreign provider may be removed from default distribution only after architecture and failure-parity gates pass.

## Release Profiles

- `debug`: symbols, stack traces, profiler hooks, and required unwind metadata.
- `release`: optimized, stripped debug data, compact diagnostics/unwind where required.
- `release-small`: NoGC where selected, hidden exports, section GC, ICF, `as-needed`, no exceptions/unwind/RTTI only with `NoUnwindProofV1`.

## Feature Preservation

Optimization changes admission and loading time, never feature semantics. Any feature omitted from the base closure remains available through a sealed provider. Any uncertain dependency stays retained and is named in the receipt; the compiler never guesses it away.
