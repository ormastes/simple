# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6365`
- tracker_sha256: `a5d99baca3561a34c1381106bf6b8b0b3f03931efd31ce8d1e8519a421d780fa`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4295`
- audit_sha256: `a72afc524ab2e6606548ec6001656272cefb9b416d7e7965cdb9bad13b070c92`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `23552`
- default_report_sha256: `706c9c1f7532a4eac9030ce10dea7bff766bd1af21e5f76d04e334c1fe437b9c`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `25135`
- default_env_sha256: `d2c3d507b3b8d7a3cf2d4205e06d34f4da9c247f9d385b9db53bf0d7a3bffdc6`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `bf7f6c7994534712ec5aa88294eadf5d4bdb9d49d4b1b3716f2afda76f834fce`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `a89c148e98bce0149b5fff56b0dae89768c2c33388f353c7ad2a9046c3a84d05`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `f143f3be41c17eeb28e90f285a9e91b6cb0190336f459f2b6260d86836c27df7`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
