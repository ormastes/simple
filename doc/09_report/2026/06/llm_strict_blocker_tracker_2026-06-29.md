# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `4a90af8d57a4ce5d26d965480866bad3df67c22a663656dba6684837982e7595`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `9c5c010d240421cee641a53e11590e991271edf26ccee43940b7d607000fd18d`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `18216`
- default_report_sha256: `992eff8f823e10e06505f948503dbb33aea61019b0e04dce4784cc063d5349f4`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19929`
- default_env_sha256: `eea81920a25b923480433f24762cfcb7421b9e01082907662d44fde07073d728`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `7467220ed92a59a6acd105a093063fd553f499f0eaf8c7fc43442075c1a10a8a`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `8b865e8d0a17bc20bc653f75d8ab1e320bfaa1169c0ddb90a2290351959e71d8`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `120`
- public_absence_surface_manifest_sha256: `6c8d04a0f8e90367e27ddc4f87a74ae8196b9809b03eef8ec23d61a96f795207`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
