# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6166`
- tracker_sha256: `51ffff53837e31cffa214feeffd469650bdec01ec93ee70c331fdf7bfd04f5cf`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4096`
- audit_sha256: `bb9373cc5b519e4e651361a75fa2277b783b6633ccc0a0c0603930383e618d89`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `22966`
- default_report_sha256: `275130e509e0f8b33ee2ea3cfc83fad6eb7e3036e34a133d9441b144bc6e2952`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `24549`
- default_env_sha256: `dd45ab427bcacec98943067e2785004f4dba5338b540fa1a70c345eee3414feb`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `efa49d7e0669d34f7717587ba7b181c85626a2a72d0368ff42267567c50666c2`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `4cee88ee4f5e54d7dd4ad7dafc4090a61cb94e6bb6af85c06a66a681d8a73e25`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `ac7a18280137b1d4c5a73d97f24ea2a2da10faa70f7da7083867a1872b3f1860`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
