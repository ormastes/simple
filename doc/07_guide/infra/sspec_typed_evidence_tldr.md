# Modern SSpec Typed Evidence — TL;DR

Full guide: [Modern SSpec Typed Evidence](sspec_typed_evidence.md).
For PDF/standards work, start at
[specification sources to executed evidence](sspec_typed_evidence.md#specification-sources-to-executed-evidence).

An observation is not an oracle. A capture records behavior; only an independent,
declared, fail-closed comparison checks correctness. Pin primary source editions
and hashes, map clauses to requirements, and distinguish repository policy from
standard obligations. Use real owner calls and independent expected values.

```text
EvidenceRequest -> provider -> RawArtifact -> format adapter -> CanonicalEvidence
  -> OracleSpec + comparator -> ComparisonResult -> ManualBlock[] -> spipe_docgen -> manual
```

Implemented source includes the shared model/comparator, format adapters, action
trace, spec bridge, manual renderer and E5 docgen sidecar wiring. E5 wiring is
not complete provenance enforcement: the loader does not yet gate rendering
with `evidence_manifest_is_complete`. Process/file capture providers and live
example specs exist; remaining domain-provider gaps are not a blanket absence
of live capture. `sspec-maintain evidence` commands remain designed/unimplemented.
Use the full guide's implementation boundary for current scope.

The four historical red-team comparator defects are fixed in source: bind-only
vacuity, non-numeric tolerance, overflow and malformed SHA-256 text. This does
not itself prove downstream loader enforcement or current test execution.
Historical August 2026 checks used the disclosed Rust seed; they are not fresh
admitted self-hosted verification. Do not infer present runtime availability.

TDD requires observed RED then GREEN on the actual target. Tests written first
but unexecuted remain AUTHORED_UNRUN; authored manuals are not generated proof.
Generated evidence needs spec/artifact hashes and real docgen results. Label
injected failures separately from real-provider failures, and keep branch
numerator/denominator tied to the actual owner, backend and target, including
zero-hit sites. UNMEASURED is neither zero nor 100% coverage.

Use the admitted runtime's supported test route. A historical module-cap
workaround is not a universal instruction to replace `test` with `run`.
