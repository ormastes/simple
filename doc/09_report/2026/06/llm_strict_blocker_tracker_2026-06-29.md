# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6131`
- tracker_sha256: `f25f2f92deed68c4a275e9c07c7d34f4533be8d5c8aa7d200ac7ba0d7293ef2d`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3890`
- audit_sha256: `6cda47d82c06175e0f62adc443e528809959eef51e75420ff0b2d62ff527869c`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `17981`
- default_report_sha256: `9ecec225ddf92f58f01688f3b6133ddc053eddebdccb451f09f8f1e3077b783b`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19693`
- default_env_sha256: `3af54aeaa3c81350c4a9f83efa7a31c59af7d19342b91fda7beb276f13d517f7`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `9f73daa7cfebd2ce82b0ea5c03d27c26d5550fe66a5e277c58d5d0cf2c6abf41`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `133ded4adf7b7953eb00927fd0637d1f07e3e15eb613620ef8fc9ad35586e39e`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `93`
- public_absence_surface_manifest_sha256: `976c611ac8f6374448178464a3f60682db591c3c9ce5d44fc22a7e92506cc429`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
