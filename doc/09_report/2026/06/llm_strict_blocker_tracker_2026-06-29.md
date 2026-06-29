# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `15bd0990f2203c6054ad10dd130ca244d46f56bd0a4c0954b0bc8930674df241`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `a2d3d9fb30fdb69090905d664fd1ff8b66b0a9f4acbfa394666899bdf5432462`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `18080`
- default_report_sha256: `c32fff315fa6a3a80e11d5fbf0a4118b1d220cf486704ef265182bf7e615c75b`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19793`
- default_env_sha256: `cade0ab4b951004b1072e8b3c06913ff70f92196828dda75c727ee2412c2e686`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `7d1759e328cc80724b6029081e96ca0c5ddbdb7f5098e01ed6d5ad31bea8b416`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `133ded4adf7b7953eb00927fd0637d1f07e3e15eb613620ef8fc9ad35586e39e`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `120`
- public_absence_surface_manifest_sha256: `e427322375750c8277402fbe703925127138f034fce963bb08555248ec4d2242`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
