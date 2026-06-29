# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `54053fa0ed20535f7aaacb222e286dcaa99fd69f0936d8205270e9e1da8350d6`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `e814a29c793c91c3680412c6926b03a8a1f2c5703e73a31ca1f59221fe4bf433`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `19799`
- default_report_sha256: `80d9ce3a7ab28c358fcd1db084f18a886f50f2bdafa16cafa8189f044272ecb9`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `21459`
- default_env_sha256: `cc1eca437115472334b85e1e03c221c4833d459585f137f7f22f3da10078a3a9`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `b0d5fb05e47b447524403b952c6a50d5c914f62f1b2848634b48e2e464c9b513`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `c27ff364da8a4f4f11a631c9d215bfec004fdd9b368309b35926b5ecefb38496`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `cdc68e98dd7aff539e273675ea9d26806806b26a859ecd36a60d193ca5ed263a`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
