# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `b90a66fb02a6777e74ec6297395002dd0216cf0cf5498270175f617276c9b96f`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `a4cbef055106bdab588977ec7a7cded6a9d5fcbb1efadf618e487f59c84b38bb`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `18216`
- default_report_sha256: `6297a843d60ae8761748f00ca506547196911582c96eec607aa22038327b334e`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19929`
- default_env_sha256: `91c2070b84a463232af664a1cc98084cb326a721437c4ac237d40eaaaaab3ac2`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `189f36512af3a471592de81cc0644ace205dfcf6bbfa1508e1ddcb96261250c7`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `2856141918874a4cd91e61f6ddf2d78a8cfef7441de3d83613c5ab31357849ab`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `1ddd6d40375beddffb6ba1eea0e9f50ea66cf84d241902ab59516a1f0578134a`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
