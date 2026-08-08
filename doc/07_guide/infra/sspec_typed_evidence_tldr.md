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

Landed: `src/lib/common/spec/evidence/model.spl` (selectors, oracle modes, manifest,
manual blocks) and `evidence_comparator.spl` (`compare_evidence`), covered by
`test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl` (24 examples).

Fail-closed: parse error, unresolved selector, ambiguous cardinality, ignore without a
reason, all-ignore vacuity, closed-mode undeclared field, and zero positive resolutions
all FAIL. Patterns (`"hex:16"`) are anchored class tokens, never regex or substring.

Design-only so far: TUI cell capture, GUI action trace, format adapters, docgen wiring,
spec-to-spipe extension, the three reference examples (lanes E2–E8 in
`doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`).

Run it with `bin/simple run` — the `test` daemon path trips its 800-module import cap.
