# Modern SSpec Completion — Parallel Small-Agent Implementation Plan

**Date:** 2026-08-08
**Research:** `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md`
**Design:** `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`
**Process:** SPipe phases (`.claude/skills/spipe.md`, `.claude/agents/spipe/*.md`); Codex lanes via `$sp_dev`.

## Agent model

Small, cheap agents (Codex Spark / Haiku / Sonnet / GLM sidecars) do scoped implementation and verification lanes; **every lane result is reviewed by a higher-capability model (Fable/Opus) before acceptance** — verify SHAs, run receipts, and deliberate-red evidence yourself; rework goes back to the ORIGINAL lane with guidance (see memory rule feedback_review_every_subagent_result_with_higher_model). No lane self-certifies. Placeholder helpers must fail explicitly (`assert(false)`/`fail(...)`), never silently pass.

Ownership mirrors the spec-to-spipe agent rules: one shared-contract owner, one verification owner, one `spipe_docgen` integrator.

## Waves and lanes

### Wave 0 — contract + red-team gates (blocks everything)

| Lane | Exclusive ownership | Deliverable |
|---|---|---|
| E0 Evidence contract | `src/lib/common/spec/evidence/**`, manifest schema, compatibility facade | frozen v1 evidence model + golden serialization |
| E1 Verification/red team | evidence acceptance policy, release checks | deliberate-red, stale-hash, unresolved-selector, vacuity, example-integrity gates |

Merge gate: E0+E1 agree on schema, failure semantics, deliberate-red fixtures. No other lane edits shared records.

### Wave 1 — independent domain foundations (parallel, dep: E0)

| Lane | Exclusive ownership |
|---|---|
| E2 TUI/GUI provider | ui_access/SGTTI/Draw IR/wm_compare adapters, TUI cell grid |
| E3 Text protocol | text parser, grammar adapter, selectors, structural comparator |
| E4 Binary layout | BinaryLayoutIR, PTE accessor adapter, RegisterIR/struct bridges |
| E5 Docgen skeleton | SOLE `spipe_docgen` owner: evidence loader + generic ManualBlock renderer |
| E6 Spec-to-SPipe bridge | `simple.sspec.evidence.v1` extension namespace + emitter integration (frozen Phase-0 core untouched) |

### Wave 2 — reference profiles + examples

E2/E3/E4 each land their reference profile + generated manual (deps: own lane + E5). E7 (domain profiles: 2D, 3D, simulation, audio, stats, ML) deps E0 + relevant adapters. E6 lands generated SSpec/evidence/manual fixtures.

### Wave 3 — migration, docs, final review

| Lane | Deliverable |
|---|---|
| E8 Migration/examples | three runnable reference specs, byte-identical regeneration, legacy adapter migration; never hand-edits generated manuals |
| E9 Docs/skills | requirements/design/plan/guide/skills/templates refresh (list below) in the SAME change as the executable workflow |
| E1 Final verification | independent deliberate-red + freshness review; no stale/missing/aspirational example accepted |

### Contention rules
- E0 alone changes shared evidence records; E1 alone changes acceptance policy; E5 alone changes `spipe_docgen`; E6 alone changes shared spec-to-spipe emitter integration.
- Adapter lanes own only their provider/format/comparator/test directories.
- A shared-field change needs migration + compatibility + golden update + E1 review.

## Documents and tools E9 updates together

```text
doc/02_requirements/feature/sspec_scenario_manual.md   (FR-7..FR-14 added)
doc/05_design/sspec_capture_extension.md               (replace monolithic Capture)
doc/03_plan/sspec_modernization_plan.md                (rewrite around this wave graph)
doc/07_guide/infra/sspec_scenario_manual.md            (three full examples + cookbook)
.claude/skills/spipe.md                                (decision table + 3 short examples)
.claude/agents/spipe/spec.md
.codex/skills/sp_dev/SKILL.md  + .agents/skills / .gemini/commands mirrors
.claude/templates/spipe_template.spl
```

Tool additions (extend, don't replace `simple test` / `sspec-maintain`):
`sspec-maintain evidence <spec> --explain`, `sspec-maintain verify-examples`,
`sspec-maintain scan --profile-completeness`, `simple test <spec> --update-evidence|--accept-evidence`
(new/changed evidence stays pending-review). New findings SSDOC-EVD-101..107, SSDOC-UI-101/102, SSDOC-TUI-101, SSDOC-PROTO-101/102, SSDOC-BIN-101/102, SSDOC-MAN-101 (definitions in research doc §9).

## Completion gates

The acceptance gates in research doc §10 apply verbatim: three executable reference specs; deterministic regenerated manuals bound to spec SHA-256 + run identity + artifact hashes; deliberate-red per oracle; TUI Unicode fixtures; GUI policy compliance; text protocol exact/ignore/pattern/order/multiset/correlation/malformed/closed proofs; binary via real PTE accessors; wm_compare exact gates unchanged; spec-to-spipe agreement without tautologies; skills/guides refreshed in-change. Documentation freshness is part of completion, not release cleanup.

## Immediate order

Follow research doc §11: freeze contract → red verifier → text+binary comparators → TUI grid → GUI trace → docgen projection → three examples → spec-to-spipe → domain profiles → migration → docs → independent review.
