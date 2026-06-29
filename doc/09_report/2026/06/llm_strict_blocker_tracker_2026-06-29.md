# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `03ff046bea7f4661e48ce1159c7c5bfdceb3e64b6c146d02e0c1f4d863a6a2f1`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `68007872dba8d62a75ea662b98824a612edd7d01c770c583e0b97893950433b8`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `19747`
- default_report_sha256: `119599b0f8cf5418eafee2a0d644180a0d409ea76259f5f9c02e6a6e4f270c6c`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `21407`
- default_env_sha256: `5be476babcadf51914359fe65cc3a072c1ad9405344c9c3a4ef05cec401b0b54`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `97ae2758ed0e1ed9995551a7fe4da8f4cbbd9363087c300f2e6a4c7457d09e7f`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `c2ed33a1effe09400338da702dbf6a8d0aa5d3f0408b9e379406c28c898e2863`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `4e8e48fbab87de7eb11565d95a774db3f315a5c419e7b668254b64dce32a730b`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
