# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `d886c38362c29b3c943558d8eb1a9773787c3f7052ef2021ab62995ae2919057`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `48bf722199bd7e4fcd5684b1c2175ac79bda60a674b0a2a56a4f13ee58012032`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `25715`
- default_report_sha256: `ee26cf9c313d7dbb5a1db83c691bd03e6e2ef8ec9cdda090973e12987fa1bc4e`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `29145`
- default_env_sha256: `eeff24f4c67550d0a61c080c1f4a85addf68fc37944f766f24bb0afa7830cd16`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `15`
- vllm_surface_manifest_sha256: `40af3d17017ed34fd11b0ab1cb351c543b645f0e0ce126593f1853228b090d7b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `b8ab77b70962706994780b4e48111fcc2145ba45c54e378d7f1cfb27a3c96f35`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `57428df2e4c6a9e839e4b5b67fd53c86a4c07d481ef52b22090743a4766dc82a`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
