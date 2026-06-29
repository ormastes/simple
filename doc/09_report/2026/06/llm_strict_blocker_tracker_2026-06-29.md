# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `82820c2beb6e8b1a1641222baf53fb5580ffbe91322fbd30d7154c145ec879f8`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `d7fcac2102726404dc5769fe680f62ec143b623ff82b60f1fdceef3b641d34ed`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `19799`
- default_report_sha256: `dd0d9fe23ce7e120b866db281b4c3d31b068e7d6523e68618d8a2e854420be4c`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `21459`
- default_env_sha256: `41ba8ea18feefba8cde150e0296c39dd1161d8fd240aca47e7f827d186e55f4a`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `b0d5fb05e47b447524403b952c6a50d5c914f62f1b2848634b48e2e464c9b513`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `c27ff364da8a4f4f11a631c9d215bfec004fdd9b368309b35926b5ecefb38496`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `506612dc3fec07ec39061fbf1788c00111bc8a99723176bbdb737317db175816`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
