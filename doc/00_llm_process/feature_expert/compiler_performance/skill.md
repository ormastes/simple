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

Immutable mono replay now captures the actual applied root/FIFO selection and
reconstructs complete bodies before the shared exhaustive verifier. The
`verification` fixture requires 18 checks. Borrowed post-HIR declaration/body
readers return only scalar/layout/RT/join-point DTOs; `postfacts` requires 14
checks and the managed handoff. Both fixtures remain unrun. Their public pins
and editable fact rows need genuine driver prerequisite ownership before final
admission.

The reviewed MIR declaration/default stack retains complete expression
artifacts, canonical callable/global ownership, nested `Throws` types and lifted
closure/trait metadata. Its nine unit examples and 17 native fixture checks
remain unrun; the real final repository and driver activation are still needed.
Cold SCV source admission now has a separate owned source-capture-plan factory:
it admits the pinned generation/snapshot and returns selected input rows without
HIR. Four new ownership/alias/snapshot boundary examples are unrun. This source
plan cannot authenticate the later transformed body.

Retained full-inventory SMF/witness emission now uses a per-module owned scope,
sharing its actual implementation with borrowed archive capture. It retains all
real emitted payload/file/witness outputs and original error categories; two
additional compiled-spec examples remain unrun. Full HIR graph retention and
the required cap qualification are still unresolved by this local change.

Actual streaming schedule capture binds physical surfaces, each independent
authored alias, real visit order and distinct logical/layout orders. The
`schedule` and `schedule_shard` selectors each require 13 native checks in
separate runtime processes. Shard order is prospective and refuses full
publication admission. Explicit aspect claim replay preserves ordered real
registry inputs without installing another compilation's claims. These controls
are unrun and still need the genuine transformed-stage prerequisite owner.
The narrow MIR compatibility-default detach API removes only default/ambiguity
roots and preserves return/type/link metadata; two frontend examples are unrun.
