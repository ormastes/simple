# Modern SSpec Typed Evidence — TL;DR

Full guide: `doc/07_guide/infra/sspec_typed_evidence.md`

An observation is not an oracle. A capture proves something was recorded; only a declared,
fail-closed check proves it was right.

```text
EvidenceRequest -> provider -> RawArtifact -> format adapter -> CanonicalEvidence
  -> OracleSpec + comparator -> ComparisonResult -> ManualBlock[] -> spipe_docgen -> manual
```

Landed 2026-08-08 (`src/lib/common/spec/evidence/`): `model.spl` + `evidence_comparator.spl`
(contract); E2/E2b `format/terminal_grid.spl` + `action_trace.spl`; E3
`format/text_protocol.spl`; E4 `format/binary_layout.spl`; E6 `spipe_extension.spl`;
E7a/E7b `format/scene_profile.spl` + `format/simulation_profile.spl`; `manual_render.spl`.
8 spec files / 124 examples.

Fail-closed: parse error, unresolved selector, ambiguous cardinality, ignore without a
reason, all-ignore vacuity, closed-mode undeclared field, zero positive resolutions all
FAIL. Patterns (`"hex:16"`) are anchored class tokens, never regex/substring.
**Still open** (red-team, unfixed): bind-only oracles pass vacuously, `numeric_tolerance`
accepts non-numeric operands, tolerance math can overflow into a false pass, manifest
digests aren't checked for 64 hex chars — guide §8a.

Not yet implemented: `spipe_docgen` evidence wiring (E5), `sspec-maintain evidence`
commands, live capture providers, the three reference examples (E8) — guide §8.

Run with `bin/simple run` — the `test` daemon path trips its 800-module import cap.
