# Modern SSpec Typed Evidence — TL;DR

Full guide: `doc/07_guide/infra/sspec_typed_evidence.md`

An observation is not an oracle. A capture proves something was recorded; only a declared,
fail-closed check proves it was right.

```text
EvidenceRequest -> provider -> RawArtifact -> format adapter
                                                  |
                                        CanonicalEvidence
                                                  |
                                 OracleSpec + comparator
                                                  |
                                       ComparisonResult
                                                  |
                                        ManualBlock[]  -> spipe_docgen -> user / QA manual
```

Landed 2026-08-08: `model.spl` + `evidence_comparator.spl` (contract), plus lanes E2/E2b
(`format/terminal_grid.spl`, `action_trace.spl`), E3 (`format/text_protocol.spl`), E4
(`format/binary_layout.spl`), E6 (`spipe_extension.spl`), E7a/E7b
(`format/scene_profile.spl`, `format/simulation_profile.spl`), and `manual_render.spl` —
all under `src/lib/common/spec/evidence/`, covered by 8 spec files / 124 examples in
`test/01_unit/lib/common/spec/evidence/`.

Fail-closed: parse error, unresolved selector, ambiguous cardinality, ignore without a
reason, all-ignore vacuity, closed-mode undeclared field, and zero positive resolutions
all FAIL. Patterns (`"hex:16"`) are anchored class tokens, never regex or substring.
**Still open** (red-team 2026-08-08, not yet fixed): bind-only oracles pass vacuously,
`numeric_tolerance` accepts non-numeric operands, tolerance math can overflow into a
false pass, and manifest digests aren't checked for 64 hex chars — see guide §8a.

Not yet implemented: `spipe_docgen` evidence wiring (E5), `sspec-maintain evidence`
commands, any live capture provider, the three reference examples (E8) — see guide §8.

Run it with `bin/simple run` — the `test` daemon path trips its 800-module import cap.
