# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `56f64012a7f9452bc544673571e6d68dbca948c6f5e4c181e9b134b201228893`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `ac9c1e4ae6dfe704071bb0c9ad0a1300db02a225ee9542a05019a4c0bac2867e`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `27262`
- default_report_sha256: `c4a94a699138f44e06115dfdbebe21111cf8338703f1a4a4dcaffed8dc53af1b`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `31915`
- default_env_sha256: `68b54e582173533d1d60243c455e472452068f4b1561cc8f004e2e3076f822f4`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `15`
- vllm_surface_manifest_sha256: `05f67846d07e6cd2bdc2f90afc1b01ee520fff404cbb5bdb9610676f47915667`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `19`
- torch_surface_manifest_sha256: `f3cff8e65d26227ae70e7985542710932954a142acc5d68b5878d0b5cc837cde`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `ee9ea8b92083a32a5b03ba5eb7a94a4327b1bbd08d12cbdc2332eaa7c70baed8`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
