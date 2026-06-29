# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `5818`
- tracker_sha256: `b6f7f14f201a324dfa723ac48ccd8651afca1640067893ba4be9fa2e79fdc710`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3890`
- audit_sha256: `e24e62b468258abc3238141b6e3a1abd2886a0100dc0c7d9522e30dd93813f46`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `16936`
- default_report_sha256: `f3e5e38b570ea367efe4b8147f1af7d230ea39b4da02f7cd1f0397aabb98d113`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `18648`
- default_env_sha256: `4beac0587c23a794103a0ca679d6957ad24015a54197196672645d5aa934d3da`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `9b85d129def40b7c89806c870829fbb612efbde1ff410392bfa54e4c33ac194c`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `f7380104165ed45c8a3341c3ca1af672c50bfcf15bd3c5273009f60c2d4f505f`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `93`
- public_absence_surface_manifest_sha256: `4548f884a84f5b5e1c1f09183f237bc991c5170fd5ef180d101fe420d5b590ad`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
