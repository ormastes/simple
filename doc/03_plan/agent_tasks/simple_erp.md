<!-- codex-design -->
# Simple ERP Agent Tasks

- Sidecar lanes: N/A for this seed.
- Merge owner: Codex.
- Final reviewer: normal/highest-capability review before release.
- Current task: expand the in-memory ERP example, SPipe coverage, and matching
  docs without touching unrelated dirty files.
- Submodule status: local submodule registered at
  `examples/12_business/simple_erp` because the expected GitHub remote is
  absent.
- Submodule-local docs: `doc/feature_plan.md`, `doc/architecture.md`, and
  `doc/design.md` inside the submodule.
- Production docs: `doc/production_plan.md` and `doc/agent_teams.md` inside the
  submodule.
- Recovery docs: `doc/recovery_plan.md` inside the submodule.

## Work Items

1. Align architecture, design, and feature-plan docs to the CRM/reservation/
   selling split.
2. Describe easy mode as the operator-facing summary and pro mode as the
   numeric control view.
3. Keep the example explicitly in-memory and single-file until a real storage or
   routing need appears.
4. Preserve the six-hour implementation shape so the docs can hand off cleanly
   to a later persistence/UI pass.
