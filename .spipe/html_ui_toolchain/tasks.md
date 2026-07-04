# html_ui_toolchain — Task Breakdown & Model Assignment

Orchestration: small tasks run on small models (haiku/sonnet), every wave is
reviewed by the big model (Fable orchestrator) before commit. Parallel agents
get disjoint file scopes (hard rule — same-dir agents clobber each other).

## Wave 0 — Research (parallel, RUNNING)
| ID | Task | Model | Scope (writes) |
|----|------|-------|----------------|
| R1 | Web: classless CSS theme candidates + element catalog | haiku | doc/01_research/ui/html_ui/css_theme_candidates_2026-06-12.md |
| R2 | Repo: SMF emission/size, dynSMF build lane, reusable HTML/CSS parser APIs | sonnet | doc/01_research/ui/html_ui/smf_ui_builder_internals_2026-06-12.md |

## Wave 1 — Design (big model, after Wave 0)
| ID | Task | Model | Scope |
|----|------|-------|-------|
| D1 | Architecture: core lib API contract, artifact format (std vs dyn parts vs merged, main-file element→part map), CLI surfaces | fable (orchestrator) | doc/05_design/ui/html_ui/html_ui_toolchain.md |

D1 fixes the API contract so Wave 2 tasks can run in parallel against it.

## Wave 2 — Implementation (parallel, disjoint scopes)
| ID | Task | Model | Scope (writes) | ACs |
|----|------|-------|----------------|-----|
| T1 | Core lib: HTML+CSS pair model, parse/serialize (reuse existing parsers per R2), element catalog | sonnet | src/lib/common/ui/html_ui/ | AC-1..4 base |
| T4 | Theme assets: full-primitive-catalog HTML+CSS theme (per R1) | haiku | src/lib/common/ui/theme_html/ | AC-6 |
| T6a | Guide skeleton: structure + editor/builder/verify sections stubbed | haiku | doc/07_guide/ui/html_ui/llm_html_ui_guide.md | AC-7 |

## Wave 3 — CLIs + integration (parallel after T1)
| ID | Task | Model | Scope (writes) | ACs |
|----|------|-------|----------------|-----|
| T2 | ui_edit CLI: new/set-css/add-element/list, multi-CSS, round-trip preserve | sonnet | src/app/ui_edit/ | AC-1, AC-2 |
| T3 | ui_build CLI: --form=std/dyn, <4KB parts, main map, merge decision, --verify oracle | sonnet | src/app/ui_build/ | AC-3, AC-4 |
| T5 | Build-lane integration: dynSMF build-plan entry + background compile evidence | sonnet | (files per R2 finding; declared at wave launch) | AC-5 |

## Wave 4 — Specs + review + polish (parallel, then big-model review)
| ID | Task | Model | Scope (writes) | ACs |
|----|------|-------|----------------|-----|
| S1 | SPipe specs: editor | sonnet | test/.../ui_edit_spec.spl | AC-8 |
| S2 | SPipe specs: builder + verify pass/fail | sonnet | test/.../ui_build_spec.spl | AC-8 |
| T6b | Guide completion incl. TUI CSS-degradation notes | sonnet | doc/07_guide/ui/html_ui/ | AC-7 |
| REV | Big-model review of full diff, lint/check gate, fixes | fable | all | AC-9 |

## Standing constraints injected into every implementation agent prompt
- Interpreter-mode verification only (`bin/simple test ... ` default mode); compile modes false-green.
- `export Name` statement form; no inheritance; generics `<>`; arrays are value types.
- No named-arg calls; `expect(x).to_equal(true)` not bare expect.
- Tests may need `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`.
- Commit nothing themselves; orchestrator commits per wave after review.

## Pending decisions (blocked on R2)
- P1: if minimal real SMF > 4 KB, dyn parts use SMF-wrapped raw data sections or a sidecar blob format — decide in D1.
