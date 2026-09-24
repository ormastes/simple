<!-- codex-research -->
# Pure-native binary footprint — domain research

Status: research complete; options only.  This feature has sufficient primary
in-repository evidence for the decision now, so no web claim is needed.  Future
implementation should use the platform/linker primary documentation for the
selected target and record the exact tool version in its receipt.

## Applicable domain practices

### Closure is a dependency decision, not a post-link hope

Dead-section collection, stripping, and dynamic-link flags can reduce an
artifact, but they do not prove why a provider was selected.  A sound native
footprint contract first resolves a typed, target-specific provider manifest to
a unique, closed symbol/provider set.  The linker is then a second line of
defense.  This matches the selected optional-provider requirement for exact
entry closure and the draft's proposed fixed-point provider closure.

### A split is not a deletion

Moving a compiler or optional provider out of the primary executable may shrink
that file while leaving installed bytes unchanged or larger.  Fair evidence
reports separately: primary artifact bytes, runtime-closure bytes, provider
bytes, deduplicated installed total, mapped files, and actual RSS.  A receipt
must say whether a provider was merely installed, mapped, initialized, or used.

### Measurement is a cohort, not a single timing

Fresh-process startup and RSS are noisy.  The selected repository contract is
at least 30 samples for development and 100 for release, with a deterministic
interleaving, raw rows, p50/p95, maxima, failures, and provenance.  This
supersedes the 15-sample draft proposal.  Warm/cached measurements may inform
diagnosis only when labelled; they must not be mixed into fresh-process
admission rows.

### Native boundary honesty is required for safety and portability

“Pure native footprint” means reducing accidental closure and duplicate
ownership, not replacing platform mechanisms.  Executable mapping/W^X,
relocation/raw calls, host TLS/trust/socket leaves, GPU/device APIs,
window/display/event systems, audio/browser/backend loading, and ABI marshalling
remain explicit native capability boundaries.  Optional absence must fail
closed with the compatible typed error rather than a nominally pure success.

### Receipts are supply-chain objects

An admission receipt needs immutable identity for the source state, compiler,
manifest(s), build command/environment/cache policy, artifact and link map,
binary reader, dynamic dependencies, and sample evaluator.  A pair-level
admission receipt must bind source-matched control and candidate receipts,
profile/workload manifests, policy digest, and per-NFR verdicts.  It also needs
bounded output/time/result budgets and a canonical digest (and signing policy if
used).  A narrative, fixture, symbol-size sum, or stale audit cannot be
substituted for that object.

## Repository-primary references

- `doc/04_architecture/binary_footprint_attribution_v2.md` — exact-produced
  artifact binding and refusal of fixture-only admission.
- `doc/05_design/binary_footprint_attribution_v2.md` — candidate/baseline and
  shared-runtime accounting model.
- `scripts/check/check-runtime-binary-size-startup-cohort.shs` — selected 30/100
  cohort, raw sample, NoGC/provider, and C/Python comparison enforcement.
- `scripts/check/check-binary-size-go-parity.shs` — reproducible artifact,
  compiler provenance, toolchain, strip, and semantic-equivalence checks.
- `doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md`
  — selected optional-provider and binary-size contract.

## Evidence boundary

`901b3fa290c` is not a source of selected requirements.  Its design usefully
identifies closure, lazy-provider, and receipt topics, but lacks cited immutable
audit receipts and conflicts with the selected 30/100 sampling floor.  Treat it
as a proposal to be revised after the user chooses an option.
