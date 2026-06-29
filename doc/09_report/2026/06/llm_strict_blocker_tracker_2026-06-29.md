# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `5415`
- tracker_sha256: `91bb121214656d00052a4fde471d1e92e1c1a57d22a954f1c17c07dafcb1a47e`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3643`
- audit_sha256: `461a4014acb49adc9ee2a0f4ddf1c89b4f66f88df778f4b777f85b980a684cfc`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `16149`
- default_report_sha256: `4ffaa8c92aa5134fbdf702a9b8e431fe56711092a6441cb2a4a2ed99bc633d29`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `17861`
- default_env_sha256: `44a1bccae92d4629f65ccef2c46cb34d2ed6e572824b753f0fbacde44f049767`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `10`
- vllm_surface_manifest_sha256: `83abdc5c0a155eb8bc2cd2c20e3a9349d0e5b43cacf1073c5d59706b5fe9500b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `14`
- torch_surface_manifest_sha256: `852a1c814199286c0cf686f2bc68ffc8fb946a85691426a4c7440cf69aa7165c`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `93`
- public_absence_surface_manifest_sha256: `a893171fbbc6c35f8d4d9529f7ca7e3c7580d90885effad17f2001fefec81f42`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
