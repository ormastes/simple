# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `7e1ba61aa447adc5fd3d80eb83dda4ac28c4dbb76d7fec60e47f34d4ba5268dd`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `fa7e74a44b45899f80f7a7bdb0cf65448a1084db8c005308f80941158ec0f961`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `28133`
- default_report_sha256: `da6a6c5223c8bd8879f39676de2658e1461524a6d2f27846eff261265acd04c1`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `33397`
- default_env_sha256: `fc26d1c8757f4a1c105c7a1345a41fdb799e5aae7a241407f478eeed633754d7`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `15`
- vllm_surface_manifest_sha256: `815ec0d5b537abadafe21caa026327c453e2a4cc6a3be2d485fbc03fa58d466c`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `19`
- torch_surface_manifest_sha256: `617980c0ef42725f88c18981e263cc9976b9ea9fd6c8bf966995acf3ef288861`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `27cbe6bad4b3c027ba49d2754c6b8006e912e8b1d33c8a553736376c531d0e90`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
