# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6166`
- tracker_sha256: `7ef8c0c876943eb7aca4f35a72beaa14953fd0aeea5a53a9fb9851928b0cd15d`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4096`
- audit_sha256: `0baa7df284a0f41b43fe7c61cc90ff4920731df6008c7c203949688c074adea9`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `22966`
- default_report_sha256: `e0cebc2b512c1095d94e45237f43f19b86baa47f1647f6d10f8a86ccb3eb815b`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `24549`
- default_env_sha256: `7ecc2e54798d655f8c783934fb7e59b532aabac3fcffccae6be25c2f8be98b4c`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `fd1cdc29be90b82f9efcc62028db8efbb68bd230efc68a5f3cf68988cbb28000`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `729785616d2f921cc2e53762bd9589960aceecd0a618418c27180a48b6e00e66`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `3a0ef9ab82cd167763233f148adbdd61518efb0716d0107452335e8d215ded89`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
