# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `632908cde50246c347a38ccaa7f56abb157c6ca00e8f4da1fb54776af8272f86`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `056aa43499dd9a7d1e635a72115a91affdaf8cd71064908e4612e09fb6d7b9db`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `29612`
- default_report_sha256: `b22e5777fa28899794383a1238fcd7b11e1e494acf5d5a042caad6dd95ed0985`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `34876`
- default_env_sha256: `53863f393f538a65bce86d8ebf37c7070fa77e7800a1f18d594c830cf757194b`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `15`
- vllm_surface_manifest_sha256: `9571bfd9aa7148b23a6ebcf7ba5539bf290b9b02c2d2034e04fa8019f7a8842f`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `19`
- torch_surface_manifest_sha256: `3b8aff56a00b45bb3058d00aa11348bb894ca41c36e0248060812d2ba84c86c7`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `123`
- public_absence_surface_manifest_sha256: `42efb9a19eddacd1371b8bb24091dab09ab7a8c7dbda20623d3edefddcd83009`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
