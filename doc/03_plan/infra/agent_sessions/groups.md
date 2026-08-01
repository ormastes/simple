# Agent Session Groups — tmux A / E / BCD

Lane registry. Old codex sessions are un-resumable (their July rollouts are
archived at `~/.codex/sessions_archive/2026/07`); each active lane restarts as
a FRESH codex session in the main WC, seeded by its plan doc. DONE lanes keep
their row (pane closed) so the feature can be re-checked later.

## Group A (07-31 burst)
| lane | agent | old session | new session | plan doc | status |
|------|-------|-------------|-------------|----------|--------|
| mdsoc/arch | claude | 9c9a2b4d-3a22-4373-8d93-73560a00a07f | (resume) | — | active |
| clobbered-files | claude | 799e4983-7975-46d8-857f-65a8dc0f21bd | (resume) | — | active |
| resolve-contract | claude | 190b415f-98e4-435e-8541-b3c258ec2552 | (resume) | — | active |
| layout-web | codex | 019fb81f-113c-7be1-b3f5-16e42f563cf2 | — | layout_web.md | **NOT DONE** (plan-audit 2026-08-01). Branch `layout-web-layout-interface-clean` (tip 410d3d47482) still NOT on origin/main + violates no-branches rule. Lane phase is `implement-source-done`: **no runtime PASS at all** (binary lacks `check`/`test`/`spipe-docgen`) ⇒ AC-8/AC-10 unmet, AC-9 manual never generated; AC-7 GPU crossover evidence + renderer-session wiring deferred. Branch also carries 7 unrelated gpu-mmu commits and is BEHIND main's web_layout_manager state — land file-by-file, never merge wholesale. See layout_web.md |
| parser-framework | codex | 019fb81d-ceed-75e0-8b10-001fdf3da636 | pending | parser_framework.md | restart pending (Spark quota until Aug 7) |
| gpu-mmu | codex | 019fb820-8a23-7f51-b426-654814398be4 | pending | gpu_mmu_lane.md | restart pending |

## Group E (ancients)
| lane | agent | old session | new session | plan doc | status |
|------|-------|-------------|-------------|----------|--------|
| stage4-spdev | codex | 019f9c04-8a43-7092-9179-b4f4e6a62a7c | pending | stage4_spdev.md | restart pending |
| browser-harden | codex | 019f9d91-6d58-7151-a761-4ffbe943f252 | pending | browser_harden.md | restart pending |
| no-deploy-guard | claude | 0cc17245-8e37-4666-9b9d-9106c84b9a47 | (resume) | — | active ("do NOT deploy") |
| gpu-backends | codex | 019f3f17-db11-77c2-a493-5be4e71b0532 | pending | gpu_backends.md | restart pending |

## Group BCD (07-27..30)
| lane | agent | old session | new session | plan doc | status |
|------|-------|-------------|-------------|----------|--------|
| evidence-showcase | codex | 019fb154-1d06-72e2-b02e-7e32add978a1 | pending | evidence_showcase.md | restart pending |
| l4-stage-a | claude | 243d611f-3f40-4b9b-ab73-cf4b57ac4e66 | — | l4_stage_a.md | **PARTIAL — prior row was WRONG** (plan-audit 2026-08-01). **DO NOT land 926515796c6**: empty subject, 504 files, 34,700 deletions = stale-WC clobber. Real work IS on main (44b41ef9f56c, bd1a953e6952). Phase 2 img/parent_id/iframe closed; MISSING: texture_registry spec 6/10 failing yet still on main, `draw_gradient_rect_stops` defined nowhere, draw_ir_adv_spec baseline unmeasured, no pixel-parity corpus, Phase 0 determinism + Phase 3 tooling still block, goal items 2/4/6 (panels, Vulkan/CUDA offload) never reached |
| l1-pair-a | claude | 895f85cb-815f-448b-86ed-4708de028caa | (resume) | — | active |
| l1-pair-b | claude | 7e7fdac9-2661-4cde-a2e6-a253b97441fc | — | l1_pair_b.md | **CORE DONE, follow-up needed** (plan-audit 2026-08-01). All 20 ledger shas + closure ae51a5aa on origin/main. MISSING: DoD#9 third-party out-of-process is a status string only (`host.spl:552`), DoD#14 8 `ThemeId.IOSLight` hardcodes + ThemeService unlanded, `LanguageProviderRegistry` 0 occurrences (4 API requests unfiled), 4-spec RE-VERIFY QUEUE open, guest-QEMU theme gate + board evidence never run, F7 bug never filed |
| dict-values | claude | 0bc1049d-2308-469c-af22-e7321e47b199 | — | dict_values.md | **PLAN DONE, HARDEN PARTIAL — sha was WRONG** (plan-audit 2026-08-01). 6019def3307 is a DrawIR-docs commit, unrelated; real landings are 8eacdf29f2c / bd0b854606f / 50bb759cae8 / e479811c547. MISSING: `_seal_ambient_spawn_on_boot()` returns false (enforcement OFF), l4_fast_ipc still a model, no child-CSpace injection, VFS not collapsed, `lld_static` never built, mmap/pthreads open, Phases 7-8 blocked, interpreter place model unfixed |
| lint-spec | claude | 79b2040e-4c78-4cc4-bdcb-deac69deb1a8 | — | lint_spec.md | **BATCH 1-2.5 DONE, GOAL OVERSTATED** (plan-audit 2026-08-01). 89/89 shas verified on origin/main. But `.spipe/mission_critical_harden/state.md:8` claims "ALL AC MET" with phases 4-8 unchecked. MISSING: the directive's headline **.md-link lane B2-B5 does not exist at all** (no semantic_link, no W-DOC-AST-001, rename is .md-blind) — deferred, never de-scoped; Lean C2-C5 stubbed; Rust ledger (E) and ISA registry (D) absent; trust manifest doc-only; FAILOPEN1 (`simple test` exits 0 on bad path) still live |
| release-beta | codex | 019fb160-28ef-7490-a0ab-c37186bcfe1c | pending | release_beta.md | restart pending |

## CLI (start/resume per lane; # DONE = goal met, pane closed, row kept for re-check)
```sh
C="claude --dangerously-skip-permissions --resume"
X="$HOME/dev/pub/simple/bin/codex --yolo"
P=doc/03_plan/infra/agent_sessions

$C 9c9a2b4d-3a22-4373-8d93-73560a00a07f                                  # A mdsoc/arch
$C 799e4983-7975-46d8-857f-65a8dc0f21bd                                  # A clobbered-files
$C 190b415f-98e4-435e-8541-b3c258ec2552                                  # A resolve-contract
$X "Read $P/parser_framework.md then continue this lane. (main WC)"      # A parser-framework
$X "Read $P/gpu_mmu_lane.md then continue this lane. (main WC)"          # A gpu-mmu
$X "Read $P/layout_web.md then continue this lane. (main WC)"            # A layout-web  # REOPENED by plan-audit

$X "Read $P/stage4_spdev.md then continue this lane. (main WC)"          # E stage4-spdev
$X "Read $P/browser_harden.md then continue this lane. (main WC)"        # E browser-harden
$C 0cc17245-8e37-4666-9b9d-9106c84b9a47                                  # E no-deploy-guard
$X "Read $P/gpu_backends.md then continue this lane. (main WC)"          # E gpu-backends

$X "Read $P/evidence_showcase.md then continue this lane. (main WC)"     # BCD evidence-showcase
$C 895f85cb-815f-448b-86ed-4708de028caa                                  # BCD l1-pair-a
$X "Read $P/release_beta.md then continue this lane. (main WC)"          # BCD release-beta
# All four rows below were re-opened by the 2026-08-01 plan audit; each lane
# doc now carries a "## Plan audit 2026-08-01" list of concrete next steps.
$C 243d611f-3f40-4b9b-ab73-cf4b57ac4e66                                  # BCD l4-stage-a  # see l4_stage_a.md
$C 7e7fdac9-2661-4cde-a2e6-a253b97441fc                                  # BCD l1-pair-b   # see l1_pair_b.md
$C 0bc1049d-2308-469c-af22-e7321e47b199                                  # BCD dict-values # see dict_values.md
$C 79b2040e-4c78-4cc4-bdcb-deac69deb1a8                                  # BCD lint-spec   # see lint_spec.md
```

Update the "new session" column with the id codex prints (or the newest file
in `~/.codex/sessions/2026/08/`) after each lane starts.
