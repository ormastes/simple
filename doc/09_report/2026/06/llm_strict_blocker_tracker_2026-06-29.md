# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `8455ba31ecbc60a376b4cc2a0223ff948834a1579b375fbefcba268fa982c108`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `9425d7517f6fc386cdd47554907483473cfd4f742aaa5d58d1e82fe57ac9f957`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `23552`
- default_report_sha256: `b2a1cd8ceeebc834cd63295536ac8c8e26797bb30bda4019340c47d3698c2094`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `25135`
- default_env_sha256: `dbf93866185f86e19fc6398286b3d241748fe59a370dc4068f8e292820e50098`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `10a1c080d76b9840a24eaa0bb179987c8517f9ab8740f3491fc8c2724fbbd59b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `9c768de060b1e0c89eb729cd8d4be8535317cea1d58bfe92506d556390e08d14`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `4c520234efc73fd851c4d12b1451975cb2b873336dedb8c6657703c20d8bde99`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
