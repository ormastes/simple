<!-- codex-design -->
# Project Statistics Quality Reporting Agent Tasks

- Lane A: `StatsInventoryV2` and fixture-backed classification tests.
- Lane B: quality evidence adapters and truthful unavailable/stale tests.
- Lane C: Markdown/TLDR/SimpleOS slide projections and Office conversion checks.
- Merge owner: primary Codex session.
- Final reviewer: primary highest-capability Codex pass.
- Sidecars: three bounded lanes above; broad acceptance and done marks remain with merge owner.
- Frozen manual steps: `Collect the owned inventory`, `Review test evidence`, `Review quality evidence`, `Generate presentation artifacts`.
- Setup/checkers: `setup_statistics_fixture`, `check_project_matrix`, `check_test_surfaces`, `check_quality_evidence`, `check_presentation_artifacts`.
- Any unfinished helper must call `fail(...)`; silent placeholders are forbidden.
