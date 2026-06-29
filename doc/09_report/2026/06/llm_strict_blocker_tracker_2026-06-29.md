# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `037bd6ef2cc4db932a6ff9d2858dd9ace632081079d537c5373fbc9903ef2694`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `4b2af70d459b1270d4064052b26f0d1f842162821080f8ade3e1977082a49165`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `29058`
- default_report_sha256: `0fe880a411138e0b22846e7045d60e698abfc6dd86245c3ed32b9ce5426f5ec6`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `34322`
- default_env_sha256: `68c3835eff5ababe3b4d777aab3bb94437aea4e90f8764413b06e7d41ed978a4`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `15`
- vllm_surface_manifest_sha256: `d5e832329fd363e592a7989a23e24786e6071d9c8e1a2bf2e81c7dbd757fb451`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `19`
- torch_surface_manifest_sha256: `617980c0ef42725f88c18981e263cc9976b9ea9fd6c8bf966995acf3ef288861`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `eaab8ea648e86ed763b86d97febcc9d361ba283497902401900442e5bd5d3b6d`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
