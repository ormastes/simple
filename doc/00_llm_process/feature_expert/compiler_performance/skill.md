# Compiler Performance Expert

## Scope

Own optimizer activation truth, performance/memory diagnostics, shared MIR facts,
CollectionPlan decisions, symbolic summaries, and profile correlation.

## Non-negotiable rules

- Inspect requested and effective pipelines separately.
- Never activate a dormant pass mechanically.
- Treat `Unknown` alias, effect, escape, trip-count, and lifetime facts as rejection.
- Use source warnings for likely application mistakes and remarks for compiler decisions.
- Profiles affect priority and profitability only, never transformation legality.
- Preserve order, errors, traps, numeric semantics, ownership, destruction timing, and ABI.
- Reuse `PerfFacts`; do not add private CFG/loop/alias scans to a pass.
- Require positive/negative sentinels, verification, idempotence, and differential evidence.
- Run only an admitted pure-Simple binary and retain its stage/hash/provenance.

## Primary references

- `doc/01_research/local/simple_compiler_performance_memory_efficiency_audit.md`
- `doc/04_architecture/simple_compiler_performance_memory_efficiency.md`
- `doc/05_design/simple_compiler_performance_memory_efficiency.md`
- `doc/07_guide/compiler/performance_diagnostics.md`
- `doc/03_plan/sys_test/simple_compiler_performance_memory_efficiency.md`

## Review questions

1. Is the pass operational status honest?
2. What exact facts prove legality, and how are they invalidated?
3. Is the opportunity a lint, transform, remark, deep analysis, or profile finding?
4. Are uncertainty and rejection reasons serialized?
5. What positive and adversarial witnesses prove behavior?
6. What before/after compile-time, runtime, allocation, copy, and RSS evidence exists?

## Phase 3 archive journal (2026-10-12)

`driver_hir_archive_journal_v1` records real declaration publication and logical
aliases. Its source/history encoding and verification run in owned scopes; only
compact results escape. Native qualification uses the `journal` selector in
`scripts/bootstrap/tests/hir-body-typecheck-lease-native.shs` and requires 13
checks plus the canonical managed tool/runtime handoff. Execution is pending.
Journal integrity alone does not admit production order, transformed bodies or
the final MIR input. No memory improvement is established by source review.
