# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `5818`
- tracker_sha256: `7bdc4286b21d7a2bc83e3244df41a970c2e9f5bf1c00ca04948ea6d401f04827`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3890`
- audit_sha256: `403d00bbce43467e708e312208925a868fcd4f6b5230493072e479a0bac77ddd`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `17445`
- default_report_sha256: `5086d828b977fc34d788497fd8fe1ac8122a2bf7a92008fd19ec0c4a7e7010a9`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19157`
- default_env_sha256: `3c9858e3cb67571aec2c0b4f3157f10ba30aa5bd98f6b3c7fefd62a21583075f`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `a5d03b03a6b3a3cfa2d8fa5c2548d80b5ac770fd4e22a23024bb3b7a83179eac`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `94909517ac9e905a298faaaad150a40d11f0c4c30c96e6be159eed42f47df5bf`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `93`
- public_absence_surface_manifest_sha256: `83c131c28b526f8093f88d23de8073dbf771bc6c4534a1b08baaef708c5856c7`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
