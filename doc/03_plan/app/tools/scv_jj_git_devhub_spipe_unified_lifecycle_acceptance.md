# Unified lifecycle acceptance evidence

**Scope:** agent-owned observe-only base, 2026-08-25; re-audited 2026-09-05.
A diagnostic PASS below does not satisfy the production gate while
`bin/simple` is the Rust seed (`bin/simple --version` still prints the
bootstrap-seed warning). **Authoritative PASS count: 0 / 18.** AC definitions:
`.spipe/scv_jj_git_devhub_spipe_unified_lifecycle/state.md:17-34`.
Stage mapping: `scv_jj_git_devhub_spipe_unified_lifecycle_plan.md`
§ "Stage ↔ REQ ↔ AC ↔ spec cross-walk".

| Criterion | Status (2026-09-05) | Evidence or remaining condition |
|---|---|---|
| AC-1 | Source-complete; diagnostic PASS | Typed codecs (`src/lib/scv/lifecycle/entity_codec.spl`) round-trip every entity and reject schema/digest/missing/duplicate/unknown-field input. Spec `test/01_unit/lib/scv/lifecycle_entity_codec_spec.spl`. |
| AC-2 | Source-complete; diagnostic PASS | `identity.spl`; no JJ/Git importer produces an identity in production (plan Stage 1). |
| AC-3 | Source-complete; diagnostic PASS | `review.spl`; `lifecycle_gate_bundle_admits` (`:57`) has zero `src/` callers (plan Stage 0.5/2). |
| AC-4 | Source-complete; diagnostic PASS | `.spipe/policy/vcs.sdn`, `src/app/sj/lifecycle_policy.spl`; the gate manifest is not invocable against pinned BASE/HEAD (plan Stage 0). |
| AC-5 | Wired, diagnostic PASS | `bin/sj plan <legacy-argv>` routes `legacy_argv_operation` -> `vcs_operation_valid` -> `plan_integration` and prints a dry-run plan (`src/app/sj/plan_main.spl`, `bin/sj`); spec `01_unit/app/sj/legacy_argv_dry_run_plan_spec.spl` 6/6, verified red-then-green. **Two honest limits:** `sj git push` is deliberately NOT intercepted (that is `land.shs`'s path; hijacking it would break every push on this machine), and the PASS branch is unreachable because `protected_target` is hardcoded `false` with no committed protected-ref policy under `config/` — every plan today ends `FAIL — SJ_POLICY_TARGET`. Not authoritative: deployed `bin/simple` is the Rust seed. This line has now been wrong in both directions — the original claim was false, and the earlier 2026-09-05 "NOT WIRED" correction is itself superseded. |
| AC-6 | Source-complete; diagnostic PASS | `integrate_plan.spl`, `gate_manifest.spl`; zero production callers, `scripts/check/land.shs` never references them (`:72,:77,:100`). Plan Stage 0.5 item 2. |
| AC-7 | Partial, improved | `devhub lifecycle` gained `record-change` (`cmd_lifecycle.spl:99-109,:200-222`) — the first production caller of `lifecycle_store_write` — and a real `dry-run` (`:113-130`) fail-closed on absent/corrupt records. `LocalScvProvider` (`provider/lifecycle_local.spl`) is the first `LifecycleProvider` implementer; the other four traits still have zero. Specs 7/7 and 3/3, red-then-green, external sha256 oracle. Local writes only, no remote mutation. Not authoritative: deployed `bin/simple` is the Rust seed. |
| AC-8 | Source-complete; diagnostic PASS | `sync.spl`; `lifecycle_persist_sync_conflict` (`:75`) has zero `src/app` and zero `test/` callers; no outbox transport exists. |
| AC-9 | Source-complete; diagnostic PASS | `release/version.sdn`, `version_manifest.spl`; render is plan-only, no consumer migrated. |
| AC-10 | Source-complete; diagnostic PASS | `release.spl` transitions; the four SCV tag defects (plan Stage 3 T-1..T-4, `src/lib/scv/refs.spl:71-100`, `maintenance.spl:571`, `stabilize.spl:21`) mean no published tag is immutable yet. |
| AC-11 | Source-complete; diagnostic PASS | `work.spl`; no task/wiki sync exists (plan Stage 5). |
| AC-12 | Source-complete; unverified | Trace inventory spec `test/03_system/app/scv/feature/..._acceptance_spec.spl` requires all 18 rows and `# @ac:` tags; 15 executable specs exist, none skip-tagged. Authoritative run awaits an admitted pure-Simple CLI. |
| AC-13 | Blocked | Generated manuals `doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle{,_acceptance}_spec.md` are STALE (`Source SHA-256` rows at `_spec.md:199` / `_acceptance_spec.md:103` differ from the current source hashes); regenerate via `bin/simple spipe-docgen`; `sspec-maintain` cannot run on the seed. |
| AC-14 | Partial | Zero lint errors, no new raw runtime/env/process calls, files below 800 lines. Coverage and `duplicate-check` await the admitted CLI. |
| AC-15 | Source-complete | One pure-Simple path exposes typed provider traits; no OS fork. Trait implementers: 0. |
| AC-16 | Implemented for base | Research/requirements/architecture/design/plan/guide linked. Gaps recorded 2026-09-05: Stage 6a provider design absent; Stage 3 architecture absent; NFR-001/003/004/005/006/008 have no sys-test rows (plan § NFR ownership). |
| AC-17 | Source-complete | State records unaffected surfaces; generated-manual dimensions remain under AC-13. |
| AC-18 | Blocked | Diagnostic focused tests/lint green on the seed only. Production verification, duplicate scan, coverage, affected full checks and working-tree guards require the admitted CLI. |

## Promotion decision

The base is partially-wired library code suitable for continued shadow-mode
development only. It does not authorize protected-ref mutation, provider
publication, release tagging, or SCV content authority. The next change is
plan Stage 0.5 (wiring); promotion of any stage requires AC-5, AC-13, AC-14,
AC-17 and AC-18 to close with authoritative evidence plus that stage's exit
gate.
