# System Test Plan — Stronger Types: Unified `unit`, Effects, Protocol States, LSP

**Date:** 2026-11-05
**Feature:** `stronger_types_unified_unit`
**Spec:** `test/03_system/app/compiler/feature/stronger_types_unified_unit_spec.spl`
**Requirements:** `doc/02_requirements/feature/stronger_types_unified_unit.md` (REQ-UNIT-*, REQ-EFF-*)
**Acceptance matrix source:** `doc/05_design/stronger_types_unified_unit.md` §12.1

## Phased coverage

The feature lands in phases (architecture §1); each phase adds its executable coverage. This plan covers wave 1 (P1–P3). Later waves append scenarios to this spec or add focused unit specs; requirement IDs are stable.

| Phase | Wave | REQ IDs | Test IDs | Spec location |
|---|---|---|---|---|
| P1 canonical unit metadata + live registry | 1 | REQ-UNIT-01, 03, 06 | UNIT-01..UNIT-05, UNIT-09 (registry/identity subset) | this spec |
| P2 deprecation diagnostic + keyword migration | 2 | REQ-UNIT-02 | UNIT-01/02 equivalence, LSP/CLI checks | this spec + `test/01_unit/compiler/frontend/` |
| P3 effect hardening | 1 | REQ-EFF-01..04 | EFF-03, EFF-04 | this spec + `test/01_unit/compiler/semantics/effect_inference_unknown_spec.spl` |
| P4 typed endpoints / TCP typestate | 3 | REQ-CHAN-01/02, REQ-STATE-01 | CHAN-01..03, STATE-01, STATE-03 | new specs under `test/03_system/app/lib/` + unit specs |
| P5 sessions / capabilities | 4 | REQ-SESS-01/02, REQ-CAP-01 | SESSION-01..03, STATE-02 | new specs |
| P6 analysis modes + LSP/CLI/MCP | 5 | REQ-MODE-01/02, REQ-LSP-01, REQ-TOOL-01 | MODE-01/02, LSP-01..04, CLI-01 | new specs under `test/02_integration/app/` |
| P7 migration/retirement | 6 | REQ-MIG-01 | INTEGRATION-01 | migration spec |

## Wave 1 scenarios (this spec)

1. **REQ-UNIT-01 nominal role** — a canonical `unit Name: T as suffix` declaration record lands in the compile-start registry as role `nominal`, klass `Count`, identity base factor 1/1, suffix retrievable.
2. **REQ-UNIT-01 alias role** — `unit Name = Target` records role `alias` and resolves to the target's identity (no new nominal identity).
3. **REQ-UNIT-01 marker role** — `unit Name` (zero payload) records role `marker` with no underlying type.
4. **REQ-UNIT-03 distinct identities** — two nominals with identical underlying representation are distinct registry identities; neither aliases the other.
5. **REQ-UNIT-02 legacy equivalence** — the legacy `newunit_register` path produces role `nominal` facts identical to the canonical path (same entry shape, identity factor, suffix behavior).
6. **REQ-UNIT-06 no fixed cap** — registering more than 16 (use 40) distinct declarations keeps every entry retrievable by short and full symbol.

## Wave 1 unit-level companions

- `test/01_unit/compiler/semantics/effect_inference_unknown_spec.spl` (new): unhandled HIR kinds / failed callee synthesis / unresolved callees produce an explicit unknown effect or completeness=false (REQ-EFF-01, EFF-03); closure creation effects distinct from latent invocation effects (REQ-EFF-02).
- Existing specs that must turn green without weakening: `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` (its newunit scenario is deliberately RED today because the registry path has no live caller; P1 makes it pass by implementing the path, never by softening the scenario).
- Existing effect specs must keep passing: `test/01_unit/compiler/semantics/effect_inference_spec.spl`, `effect_verifier_spec.spl`, `effect_body_facts_spec.spl`.

## Matchers

Built-in only: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`.

## Execution

- Worktree: `D:/dev/simple-rt`, branch `work/simple-hardening-release-20261013`.
- Runner: pure-Simple `bin/simple` (bootstrap in progress; until admitted, no completion claim).
- `bin/simple test test/03_system/app/compiler/feature/stronger_types_unified_unit_spec.spl` (repo-relative path; absolute paths silently run nothing).
- Generated manual: `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`, then `bin/simple sspec-maintain scan` review loop per impl skill.

## Negative/deferred coverage

Compile-fail tests (dimension mismatch, invalid refined constants, state misuse) require the compile-fail harness used by existing `test/01_unit/compiler/**` negative specs and arrive with P2/P4. Session/cancellation matrices (SESSION-03) arrive with P5. Mode-gating (MODE-01/02) with P6. Recording this here so the gaps are explicit, not accidental.
