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
| layout-web | codex | 019fb81f-113c-7be1-b3f5-16e42f563cf2 | — | layout_web.md | **DONE, push VERIFIED to origin branch** `layout-web-layout-interface-clean` (tip 410d3d47482 ⊇ f80d51c1638) — **NOT merged to origin/main**, and branch violates no-branches rule; land to main + delete branch |
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
| l4-stage-a | claude | 243d611f-3f40-4b9b-ab73-cf4b57ac4e66 | — | scratchpad PHASE2_STATUS.md | **DONE but NOT PUSHED** — local commit 926515796c6 absent from origin/main; scratchpad PHASE2_STATUS.md; must land |
| l1-pair-a | claude | 895f85cb-815f-448b-86ed-4708de028caa | (resume) | — | active |
| l1-pair-b | claude | 7e7fdac9-2661-4cde-a2e6-a253b97441fc | — | — | **DONE, push VERIFIED** — sampled commits all on origin/main |
| dict-values | claude | 0bc1049d-2308-469c-af22-e7321e47b199 | — | — | **DONE, push VERIFIED** — 6019def3307 on origin/main |
| lint-spec | claude | 79b2040e-4c78-4cc4-bdcb-deac69deb1a8 | — | — | **DONE, push VERIFIED** — sampled commits all on origin/main |
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
# codex 019fb81f layout-web — pushed f80d51c1638                         # A layout-web  # DONE

$X "Read $P/stage4_spdev.md then continue this lane. (main WC)"          # E stage4-spdev
$X "Read $P/browser_harden.md then continue this lane. (main WC)"        # E browser-harden
$C 0cc17245-8e37-4666-9b9d-9106c84b9a47                                  # E no-deploy-guard
$X "Read $P/gpu_backends.md then continue this lane. (main WC)"          # E gpu-backends

$X "Read $P/evidence_showcase.md then continue this lane. (main WC)"     # BCD evidence-showcase
$C 895f85cb-815f-448b-86ed-4708de028caa                                  # BCD l1-pair-a
$X "Read $P/release_beta.md then continue this lane. (main WC)"          # BCD release-beta
# claude 243d611f l4-stage-a — done, UNLANDED (scratchpad PHASE2_STATUS) # BCD l4-stage-a  # DONE
# claude 7e7fdac9 l1-pair-b — directive complete                         # BCD l1-pair-b  # DONE
# claude 0bc1049d dict-values — landed 6019def3307                       # BCD dict-values # DONE
# claude 79b2040e lint-spec — synced+patched, verified on origin         # BCD lint-spec   # DONE
```

Update the "new session" column with the id codex prints (or the newest file
in `~/.codex/sessions/2026/08/`) after each lane starts.
