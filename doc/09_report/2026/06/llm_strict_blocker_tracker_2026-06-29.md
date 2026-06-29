# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `8e98eaa0a71126a4b8222820cecb715ac0ae930312d3ed8f44f376e90a0f6568`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `058f61cc745ffc39f3eaaf1bb20f7fdddbe0d7a6a5fe91f1e37eb873d271280e`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `19799`
- default_report_sha256: `dbb839279a178f0dd2e84edfc9bf331e8d64e70236bb15456f2b2f7261114ec8`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `21459`
- default_env_sha256: `0a154f277130641be60ed338f3a41da861627a8df0dd05b01823de6ee6a68f6d`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `08ff4da378f624b0d3d0209fd891d06c952fc2e810eb250baa004700f62d2cf9`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `b4a7d3d8b1296cc4a191d5fefeea04bb32b2dfdfdf74b7d6d8d649095b9ad52a`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `cd8e1dbf7ce385279bf75bd993d1666308d04bc36967f7d9be0c967fa0a6d83a`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
