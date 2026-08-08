# Standards Crosswalk — Simple `critical` Profile + `flight-core-v1` Convention

**Date:** 2026-08-07  
**Research base:** `doc/01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md`  
**Plan:** `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`  
**Rule registry:** `src/compiler/00.common/assurance/flight_rules.spl` (`FLT-*` definitions)

---

## Overview

This document maps Simple's `critical` profile enforcement rules (`FLT-*` IDs from the canonical registry) to external aerospace/space standards cited in the research document. Every external citation is recorded **as-cited, unverified** — network fetch is blocked in this environment, and no external standard was checked against a controlled document. This is provenance recording, not certification evidence.

**Status legend:**
- **LIVE:** Analyzer exists and is wired into a production binary that reaches users.
- **DORMANT:** Analyzer or checker exists but is not wired, or the enforcing binary predates its source.
- **INTRINSIC:** Language does not allow the violation; no analyzer needed or wanted.
- **ENFORCEMENT GAP:** Rule is specified but no analyzer exists, and the language allows the violation.

---

## Control Flow Rules

| FLT-ID | Title | External Standard | Critical Level | Analyzer | Status | Provenance |
|---|---|---|---|---|---|---|
| **FLT-CF-001** | No goto, setjmp or longjmp | P10-1 (JPL Power of Ten); JSF-AV 189; MISRA C 2012 R15.1 | Intrinsic | none | **INTRINSIC** — language grammar has no goto/setjmp/longjmp | as-cited, unverified |
| **FLT-CF-002** | No uncontrolled recursion | P10-1; JSF-AV 119; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; call-graph SCC analysis not integrated | as-cited, unverified |
| **FLT-CF-003** | Every loop has a statically known bound | P10-2; JSF-AV 191 | Shall | none | **DORMANT** — enforcement gap; loop bound inference/validation not integrated | as-cited, unverified |
| **FLT-CF-004** | Functions stay small by semantic measure | P10-4; JSF-AV 1 | Should → Will (escalates at higher grades) | none | **DORMANT** — metric collection & thresholding not integrated; intended to count semantic statements, nesting, exits, cyclomatic complexity (never source lines) | as-cited, unverified |

---

## Memory Rules

| FLT-ID | Title | External Standard | Critical Level | Analyzer | Status | Provenance |
|---|---|---|---|---|---|---|
| **FLT-MEM-001** | No allocation after initialization | P10-3; JSF-AV 206; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; allocation classifier (none/init_only/bounded_pool/unbounded) not integrated into critical flow; checker exists at `35.semantics/noalloc_checker.spl` but is not a compile gate (plan premise 7) | as-cited, unverified |
| **FLT-MEM-002** | Stack usage is bounded and known | P10-3; JSF-AV 206 | Shall | none | **DORMANT** — enforcement gap; final frame + call-chain + interrupt-nesting + coroutine-state accounting not integrated; intended to fail link if unknown | as-cited, unverified |
| **FLT-MEM-003** | Every array access is in bounds | P10-9; JSF-AV 15; MISRA C 2012 R18.1 | Shall | none | **DORMANT** — enforcement gap; HIR/MIR range proof or retained bounds-check validation not integrated into critical flow | as-cited, unverified |

---

## Data Rules

| FLT-ID | Title | External Standard | Critical Level | Analyzer | Status | Provenance |
|---|---|---|---|---|---|---|
| **FLT-DAT-001** | Data is declared at the smallest possible scope | P10-6; JSF-AV 135 | Will → Shall (escalates at higher grades) | none | **DORMANT** — enforcement gap; HIR use-range analysis not integrated; module-level mutable-global ownership validation not integrated | as-cited, unverified |
| **FLT-DAT-002** | No unencapsulated global mutable state | P10-6; JSF-AV 135; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; MDSOC capsule ownership + read/write-set analysis not integrated into critical flow | as-cited, unverified |
| **FLT-DAT-003** | Every value is initialized before use | P10-8; JSF-AV 142; MISRA C 2012 R9.1 | Shall | none | **DORMANT** — enforcement gap; definite-initialization path-sensitive analysis not integrated as a critical gate | as-cited, unverified |
| **FLT-DAT-004** | No dummy initializer hiding a missed assignment | P10-8 | Will → Shall (escalates at higher grades) | none | **DORMANT** — enforcement gap; write-before-read detection (placeholder-default suppression) not integrated | as-cited, unverified |
| **FLT-DAT-005** | Return values and resource handles are checked | P10-7; JSF-AV 115; MISRA C 2012 D4.7 | Shall | none | **DORMANT** — enforcement gap; Result/status/handle must-use validation not integrated as a critical gate | as-cited, unverified |
| **FLT-DAT-006** | External inputs are validated at the boundary | P10-7; JSF-AV 114; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; refinement-type/`in:` contract/domain-type/explicit-decoder validation at FFI/MMIO/message/storage boundaries not integrated | as-cited, unverified |
| **FLT-DAT-007** | Arithmetic is proved or checked | JSF-AV 164; MISRA C 2012 R12.2; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; overflow/div-by-zero/invalid-shift/narrowing proof or runtime-check validation not integrated | as-cited, unverified |
| **FLT-DAT-008** | Floating point is deterministic | JSF-AV 202; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; fast-math prohibition + NaN/Inf/rounding/contraction policy validation not integrated | as-cited, unverified |
| **FLT-DAT-009** | Representation assumptions are explicit | JSF-AV 183; MISRA C 2012 R11.3 | Shall | none | **DORMANT** — enforcement gap; layout declaration + generated-serializer + static size/offset assertion validation not integrated | as-cited, unverified |

---

## Abstraction Rules

| FLT-ID | Title | External Standard | Critical Level | Analyzer | Status | Provenance |
|---|---|---|---|---|---|---|
| **FLT-ABS-001** | Macro and compile-time expansion is resolved before analysis | P10-8; JSF-AV 26; MISRA C 2012 D4.9 | Shall | none | **DORMANT** — enforcement gap; macro/AOP/conditional-variant expansion & retention not integrated; unresolved conditional-variant error not a gate | as-cited, unverified |
| **FLT-ABS-002** | Indirect call target sets are closed | P10-9; JSF-AV 159 | Shall | none | **DORMANT** — enforcement gap; callback/trait-dispatch/event/DI/AOP target-set closure analysis not integrated | as-cited, unverified |
| **FLT-ABS-003** | Raw pointers live only inside a reviewed boundary | P10-9; JSF-AV 215 | Shall | none | **DORMANT** — enforcement gap; SFFI/MMIO/backend-pointer confinement to unsafe/representation boundary not integrated as critical gate | as-cited, unverified |
| **FLT-ABS-004** | No unhandled escape from the critical closure | JSF-AV 208; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; panic/unchecked-trap/uncaught-error escape validation not integrated; typed Result/enum recovery requirement not enforced | as-cited, unverified |
| **FLT-ABS-005** | No deep or ambiguous inheritance | JSF-AV 87; JSF-AV 94 | Intrinsic | none | **INTRINSIC** — language has no inheritance; composition/traits/mixins only. Ambiguity covered by FLT-ABS-002 | as-cited, unverified |
| **FLT-ABS-006** | Dynamic binding is closed-world in a flight build | JSF-AV 159; ECSS-Q-ST-80C | Shall | none | **DORMANT** — enforcement gap; loader-plugin/AOP-weaving/late-binding prohibition not integrated; closed-world constraint not verified | as-cited, unverified |
| **FLT-ABS-007** | Casts are explicit and validated | JSF-AV 185; MISRA C 2012 R11.3 | Shall | none | **DORMANT** — enforcement gap; representation-conversion/FFI-layout cast validation (size/alignment/range) not integrated | as-cited, unverified |
| **FLT-ABS-008** | Every provider in the closure is qualified | ECSS-Q-ST-80C; JSF-AV 8 | Evidence (compile), Shall (aero-a/space-a) | none | **DORMANT** — enforcement gap; per-symbol qualified-dependency manifest entry validation not integrated; weak/fabricated provider rejection not enforced | as-cited, unverified |
| **FLT-ABS-009** | The supported configuration set is enumerated | ECSS-Q-ST-80C; MISRA C 2012 D4.9 | Evidence (compile), Shall (aero-a/space-a) | none | **DORMANT** — enforcement gap; configuration enumeration & test/proof coverage per release configuration not validated at gate time | as-cited, unverified |

---

## Match Coverage Rules

| FLT-ID | Title | External Standard | Critical Level | Analyzer | Status | Provenance |
|---|---|---|---|---|---|---|
| **FLT-ENUM-001** | Every variant of a closed enum is covered | research S7 | Shall | none | **DORMANT** — enforcement gap; type-resolved `ResolvedMatchCoverage` (keyed by scrutinee_type_id + enum_symbol_id + variant ids) not integrated; missing-variant error not a gate (plan premise 11). Text EasyFix fires instead of diagnostic | as-cited, unverified |
| **FLT-ENUM-002** | No wildcard arm on a closed enum | research S7 | Shall | none | **DORMANT** — enforcement gap; wildcard rejection not integrated; lint rule `wildcard_match` is inert (set to "allow"). MIR lowering refuses to lower incomplete critical match only under blocked stage-3 (plan premise 10d) | as-cited, unverified |
| **FLT-ENUM-003** | No duplicate or unreachable match arm | research S7 | Shall | none | **DORMANT** — enforcement gap; duplicate/unreachable-arm detection not integrated into critical flow | as-cited, unverified |
| **FLT-ENUM-004** | An @evolving enum has an explicit Unknown arm | research S7 | Shall | none | **DORMANT** — enforcement gap; `@evolving` enum Unknown-arm validation not integrated; enforcement plan premises 10a-d reveal no sound pre-execution check exists | as-cited, unverified |
| **FLT-ENUM-005** | Invalid discriminants are rejected at the boundary | research S7 | Shall | none | **DORMANT** — enforcement gap; discriminant validation at representation boundary not integrated; runtime fall-through guard remains defence only | as-cited, unverified |

---

## Implementation Completeness Rules

| FLT-ID | Title | External Standard | Critical Level | Analyzer | Status | Provenance |
|---|---|---|---|---|---|---|
| **FLT-IMP-001** | No placeholder body in a concrete function | research S6 | Shall | `lint.text.stub_impl:STUB003` | **LIVE (TEXT-TWIN)** — analyzer is the text reimplementation in `90.tools/lint/_LintMain/lint_checks.spl:495-499` (plan premise 13). Semantic checker `35.semantics/lint/stub_impl.spl` exists but is not a production gate; AST-STUB003 filtered by `entry_and_fixes.spl:124-126`. Deployed `bin/simple` is Rust seed. Placeholder markers: `pass_todo`, `pass_dn`, `pass_do_nothing`, bare `pass`, empty body, `todo(...)`, fabricated `Ok(nil)`, `_noop_` name without NoOp contract | as-cited, unverified |
| **FLT-IMP-002** | Deviating code carries a substantive rationale | research S6; ECSS-Q-ST-80C | Will (critical), Shall (aero-a/space-a) | `lint.text.required_comment:REQC001` | **LIVE (TEXT-TWIN)** — analyzer is the text reimplementation in `90.tools/lint/_LintMain/lint_checks.spl:501-545` (plan premise 12b). Weak predicate: empty, `<10` chars, or filler words. Semantic checker `35.semantics/lint/required_comment.spl` exists but is not a production gate. Deployed `bin/simple` is Rust seed. Plans WP-7 to wire semantic checker and delete text twin | as-cited, unverified |

---

## Summary

**Total rules:** 32 `FLT-*` entries  
**Intrinsic (language structure prevents violation):** 2 (FLT-CF-001, FLT-ABS-005)  
**Live analyzers:** 2 (FLT-IMP-001, FLT-IMP-002) — both text reimplementations in lint, not semantic checkers  
**Dormant (analyzer exists, not wired or predates binary):** 28 enforcement gaps  

**Critical constraint:** `bin/simple` is the Rust seed and stage-3 self-host is blocked. A new pass under `src/compiler/**` outside `90.tools/lint` produces zero user-facing enforcement until that lands. The deployed lint binary predates its own source — `.spl` edits to lint do not take effect until redeploy.

**Confidence markers:** All external citations carry "as-cited, unverified" because network fetch is blocked in this environment and no external standard was checked against a controlled document. The Aerospace Hardening Research document (§2) records the same provenance. Re-verify against controlled documents before any of this becomes certification evidence.

---

## Cross-References

- **Flight rule registry:** `src/compiler/00.common/assurance/flight_rules.spl` (WP-0, canonical `FlightRuleV1` definitions)
- **Mission-critical profile requirements:** `doc/02_requirements/language/mission_critical_profile.md` (REQ-MC-* requirements, phase tracking, implementation status)
- **Plan execution log:** `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md` § "Verified premises" (file:line evidence for every repo claim)
- **Research external precedent:** `doc/01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md` § 2 (source citations, design rationale, precedent justification)
