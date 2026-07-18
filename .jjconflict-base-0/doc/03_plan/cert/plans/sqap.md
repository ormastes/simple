# Software Quality Assurance Plan (SQAP)

Companion to `psac.md`/`sdp.md`/`svp.md`/`scmp.md` (DO-178C §11.5, §8). Target grade:
aero-d/auto-a nearest-achievable, assessed against aero-a for gap visibility.

## Purpose

Define how the project assures its software processes and outputs conform to the plans
and standards (PSAC/SDP/SVP/SCMP + the coding/design standards), and how nonconformances
are detected and dispositioned (DO-178C §8.1 objectives).

## QA activities mapped to artifacts

| QA activity (DO-178C §8.1) | Artifact / mechanism | Status |
|---|---|---|
| Standards conformance — coding | `bin/simple build lint` + `scripts/audit/{naming_consistency_audit.spl,api_consistency_audit.spl,noalloc_reachable_imports.spl,repo_hygiene_audit.spl,os_harden_audit.spl}` | present |
| Standards conformance — formatting | `bin/simple build fmt --check` | present |
| Combined quality gate | `bin/simple build check` (lint + fmt --check + tests in one gate) | present |
| Structural / architectural guards | `scripts/check/check-api-arch-guard.shs`, `scripts/audit/numbered-artifact-guard.shs`, `scripts/check-workspace-root-guard.shs` (FILE.md), `scripts/audit/direct-env-runtime-guard.shs` | present |
| Process enforcement at commit/push | `scripts/hooks/pre-commit` + `scripts/hooks/pre-push` (installed to `.git/hooks/`): FILE.md guard, secret scan, conflict-marker/`.jjconflict` block | present |
| Requirements-process assurance | `scripts/check/cert/check-req-traceability.shs` (bidirectional orphan detector, self-test PASS, writes `build/cert/req_traceability_report.md`) | present; orphan burndown open |
| Determinism / reproducibility assurance | build-twice sha256 mechanism (`238d86c` deterministic entry-shim; `cert_roadmap.md` Phase 5) | mechanism-proven, not CI-wired all targets |
| Formal-evidence integrity assurance | `scripts/check/check-lean-proofs.shs` (bans `sorry`/`admit`/`axiom` etc. across all `src/verification/` Lake projects; has `--self-test`) | present |
| Problem-report / corrective-action tracking | `bin/simple bug-add`/`bug-gen`, `doc/08_tracking/bug/*`, `doc/TODO.md` (`bin/simple todo-scan`); TODO→NOTE downgrade prohibited | present |

## Conformity review + transition-criteria monitoring

- **Conformity review** (DO-178C §8.3): `bin/simple build check` is the machine-checked
  conformity review of a configuration — it asserts lint, format, and test conformance
  before the change is considered acceptable. The pre-push guards assert the *outgoing
  configuration* is conformant (no conflict markers, no oversized/`.jjconflict` blobs)
  before it reaches the shared baseline.
- **Transition-criteria monitoring** (DO-178C §8.1(a)): the SDP transition criteria
  (`sdp.md` § Transition criteria) are enforced as hooks/gates rather than QA-audited by a
  person — e.g. no change merges to `main` without passing `build check`; a change's REQs
  must not become new traceability orphans. This is process-conformance-by-construction:
  the gate *is* the QA check.
- **Independence-of-QA note:** these are automated, author-invoked gates; there is no
  separate QA authority independently sampling life-cycle data for conformance (see gap).

## QA records

- **Verification/quality records:** `doc/08_tracking/{test,bug,todo}/*` (auto-generated
  `test_result.md`, `test_db.sdn`, `todo_db.sdn`) — the record of what passed/failed and
  which problems are open per configuration.
- **Metrics records:** `doc/10_metrics/*` (coverage, perf, dashboard) — the measured
  quality record.
- **Traceability record:** `build/cert/req_traceability_report.md` (gitignored, regenerated
  per run) — the requirements-conformance record.
- **Formal record:** the per-project PASS/FAIL table from `check-lean-proofs.shs`.
- Reports proper (`doc/09_report/*`) are temporal and NOT added to git unless requested
  (`.claude/rules/code-style.md`), so QA records that must persist live in the tracking/
  metrics layers, not in ephemeral reports.

## Independence posture

- DAL D (current target) does not require QA independence per DO-178C Table A-9. No
  independent QA authority exists today; QA is enforced by automated gates invoked within
  the same working session that authors the change.
- For any DAL C/B/A claim, QA independence (an authority distinct from development,
  auditing process conformance and signing conformity reviews) is required and **not yet
  established** — flagged with the review/analysis independence gap in `svp.md`.

## Gap to full DAL-D SQA

1. **No independent QA authority.** QA is gate-automation, not a person/role independently
   assuring process conformance and dispositioning nonconformances (DO-178C §8.1, §8.2).
2. **Audits not formally scheduled.** There is no scheduled QA audit calendar (e.g. SOI-aligned
   conformity audits, records audits); conformance is checked continuously by hooks but
   not sampled/audited on a documented schedule with sign-off records.
3. **No supplier/tool-QA oversight record** for the development tool itself beyond the
   bootstrap fixpoint — the tool-qualification evidence that would back QA's trust in
   `bin/simple` is still being built (`tool_qualification_plan.md`, task C7).
4. **QA records are pass/fail artifacts, not signed conformity-review records** — there is
   no per-milestone QA sign-off tying a configuration to an assured-conformant state.
