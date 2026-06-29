# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `7cb38f8ab026399335fa62ee53339e510f077ce093f5dac01b5f775bac8c210f`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3891`
- audit_sha256: `fee232e53c2242b9f088ecb8ca408cda27dca9b1c1800ba7d4f03cbdeac340dd`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `18079`
- default_report_sha256: `667b3d4ec3ffaf0cfb94d512c2137ae8b34c77fda8fd2c16226fe5dc997a7958`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19792`
- default_env_sha256: `b4eb0f1fce25f59261804b6bd5940975df1742241e855558dcf5d5c2032c9dc0`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `9f73daa7cfebd2ce82b0ea5c03d27c26d5550fe66a5e277c58d5d0cf2c6abf41`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `133ded4adf7b7953eb00927fd0637d1f07e3e15eb613620ef8fc9ad35586e39e`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `120`
- public_absence_surface_manifest_sha256: `ba09eb428bbfa652fe9b8dadcaa0b2324547554b822287220b66998fc0aa0f89`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
