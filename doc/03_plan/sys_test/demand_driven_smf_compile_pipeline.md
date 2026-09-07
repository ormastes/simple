# System Test Plan — Demand-Driven SMF Compile Pipeline

## Evidence classes

- Functional and fail-closed behavior: `test/03_system/compiler/perf/demand_driven_smf_compile_pipeline_spec.spl`.
- Quantitative and parent-program gates: `test/05_perf/compiler/demand_driven_smf_compile_pipeline_perf_spec.spl`.
- Manual mirrors: `doc/06_spec/03_system/compiler/perf/demand_driven_smf_compile_pipeline_spec.md` and `doc/06_spec/05_perf/compiler/demand_driven_smf_compile_pipeline_perf_spec.md`.

## Traceability

| Authority | Executable coverage |
|---|---|
| DDSM-REQ-001 through DDSM-REQ-020 | One named functional scenario per requirement in the system spec |
| DDSM-NFR-001 through DDSM-NFR-006 | One 100-sample measured scenario per performance acceptance item |
| DDSM-PLAN-P0 through DDSM-PLAN-P9 | One phase admission scenario per implementation phase |
| DDSM-STOP-001 through DDSM-STOP-005 | One injected-invalid-state cutover rejection scenario per stop gate |
| PERF-GATE-F/S/V/A/Q/J/R | One multi-run admission scenario per parent performance-program gate |

## Evidence contract

The specs invoke production evidence owners rather than reproducing decisions in tests. Each owner must emit a stable scenario receipt, use the active immutable SCV revision, identify compiler and fixture digests, and fail closed on missing or mismatched authority. Performance rows require 100 samples, matched semantics, p50/p95/p99/mean/standard-deviation/confidence interval, command lines, binary hashes, host identity, file-open and mapped-byte counters, RSS, and raw retained evidence.

The two production evidence owners now exist:

- `scripts/check/check-demand-driven-smf-compile-pipeline.shs`
- `scripts/check/check-demand-driven-smf-compile-performance.shs`

`scripts/check/check-demand-driven-smf-evidence-static.shs` proves the complete 20 REQ, 6 NFR, 10 phase, 5 stop-gate, and 7 parent-gate mapping plus the presence of static implementation owners. Its mutation guard is `test/01_unit/scripts/demand_driven_smf_evidence_contract_test.shs`. Runtime, performance, and native scenarios remain expected-red until their exact admitted receipts exist; missing fields, semantic mismatch, unsupported execution, placeholder output, or unmet thresholds fail closed. No checker synthesizes runtime PASS.

## Freshness audit

- No `pass_todo`, empty scenario body, or trivial always-true assertion is present.
- Only built-in matchers are used.
- No executable `.spl` file is stored under `doc/06_spec`.
- Existing package-index specs are narrower evidence and do not close lazy materialization, common file-view, backend promotion, matched-Go, or parent-program gates.
- Existing compiler baseline specs predate this authority and do not bind the demand-driven pipeline scenario receipts.
