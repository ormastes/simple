# SSpec-Maintain Lane-Aware Scoring

Recognition of lane-gated specs in scoring metrics to prevent SKIP-clean lanes from scoring as missing coverage.

# TODO: [sspec-maintain][P1] Enhance scoring rules to recognize lane-gated notebook specs
Lane-gated specs (using `%%mode` directives with probe/skip patterns) in SKIP-clean lanes should not score as missing coverage. The `src/app/sspec_maintain/` scoring engine should distinguish between (a) specs that are genuinely unimplemented on a lane (score penalizing), and (b) specs that are intentionally skipped on that lane via `skip:` assertions (no penalty). Current scoring treats both as coverage gaps. See design: `doc/05_design/app/tools/notebook_lanes_architecture.md` § Lane-gated specs and `doc/00_llm_process/feature_expert/notebook_lanes/skill.md`.
