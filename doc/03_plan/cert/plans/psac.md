# Plan for Software Aspects of Certification (PSAC)

Target grade: **aero-d** (DO-178C DAL D) nearest-achievable; **auto-a** (ISO 26262 ASIL A)
in parallel. Assessed against DAL A objectives in `cert_roadmap.md` so every gap above D
is visible. This PSAC is the liaison-facing summary; detail lives in `sdp.md`, `svp.md`,
and the roadmap.

## Purpose

Define, per DO-178C §11.1, the means of compliance the Simple compiler project uses to
show its software life-cycle data satisfies the objectives of the target DAL, so a
certification liaison can review and concur before Stage-of-Involvement audits begin.

## Scope

Applies to the pure-Simple self-hosted toolchain (`bin/simple`, built via bootstrap from
`src/compiler`, `src/lib`, `src/app`) as the certified *product*. The Rust seed
(`src/compiler_rust`) is bootstrap-only tooling, not certification scope, but is in scope
for the sanitizer matrix (`sanitizer_matrix_plan.md`) as a development-tool integrity
check. Vendored code (`src/compiler_rust/vendor/**`, `src/runtime/vendor/**`,
`miniaudio.h`/`stb_image.h`/`stb_truetype.h`) is excluded per the repo's owned-code scope
rule (`CLAUDE.md` § Owned-Code Scope).

## Mapped-artifacts table

| PSAC element (DO-178C ref) | Repo artifact | Status |
|---|---|---|
| Software life cycle description (§11.1(b)) | `doc/` numbered phases 01–11 (research→...→archive), `.claude/rules/structure.md` | present |
| Software development environment (§11.1(c)) | Self-hosted `bin/simple` toolchain; `.claude/rules/bootstrap.md` | present |
| Coding standards (§11.1(g), DO-178C 11.8) | `.claude/rules/language.md`, `code-style.md` | present |
| Design standards | `doc/04_architecture/**/+rule/` (per-domain architecture rules) | present |
| Static analysis / coding-standard conformance | `bin/simple build lint`, `scripts/audit/{naming_consistency_audit.spl,api_consistency_audit.spl,noalloc_reachable_imports.spl}` | present, not separately gated for JPL Power-of-10 assertion density |
| Configuration management (§11.1(k), DO-178C §7) | jj/git colocated on `main` only (`.claude/rules/vcs.md`); `FILE.md` manifest guard (`scripts/check-workspace-root-guard.shs`) | present |
| Requirements-based test process (§11.1(f)) | BDD `*_spec.spl` suite (22,875 spec files under `test/`), run via `bin/simple test` | present, coverage criterion not yet MC/DC |
| Verification process (§11.1(e)) | `svp.md`; `bin/simple build check` (lint+fmt+test) | present |
| Bidirectional traceability (DO-178C §6.1, Table A-3/A-4) | `scripts/check/cert/check-req-traceability.shs` (self-test PASS); baseline 620 REQ ids, 175 traced-down, 445 orphan-down, 244 orphan-up | scaffold landed, burndown open |
| Problem reporting / change control | `bin/simple bug-add`, `doc/08_tracking/bug/*`, `doc/TODO.md` | present |
| Tool qualification (DO-330, if a tool is verification-credit) | 3-stage bootstrap fixpoint (stage2==stage3); no ACATS/torture-analog corpus | partial — see C7 |

## Certification liaison / objectives summary

- **Certification basis:** DO-178C, objectives per Table A-1..A-10 filtered to DAL D
  (Table A-1..A-5 subset; no independence requirement, statement coverage only,
  MC/DC/decision coverage not required at D).
- **Means of compliance:** artifact review (this table) + tool output (lint/fmt/test/
  traceability checker) as objective evidence, supplemented by manual review records
  (code-review skill) for objectives without an automated check.
- **SOI schedule (proposed):** SOI-1 (planning, this doc + sdp/svp) → SOI-2 (development,
  after orphan burndown) → SOI-3 (verification, after MC/DC wiring, DAL C+ only) →
  SOI-4 (final, post tool-qualification for DAL A/auto-d claims).
- **Liaison process:** none yet formalized with an external DER/authority; this PSAC is
  the internal analog pending a real liaison engagement.

## Gap to full DO-178C DAL-D

1. Orphan burndown (445 down / 244 up) — the traceability matrix is not yet closed.
2. JPL Power-of-10 / assertion-density static-analysis gate is not separately enforced;
   folded into general lint today.
3. No externally-reviewed SOI process — this is a self-assessed liaison summary, not an
   authority-concurred PSAC.
4. Above D (aero-a/auto-d/space-a): MC/DC coverage (C1), full opt-soundness sweep (C2),
   differential fuzzer (C3), sanitizer matrix (C4), and tool qualification (C7) are all
   required and tracked as BLOCKED/queued in `cert_roadmap.md`. The stage4 wall no longer
   blocks evidence-gathering on the clean `bin/simple` (corrected 2026-07-05) — only
   seed-built stage4 redeploy and seed tool-qualification remain wall-gated.
