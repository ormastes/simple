# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6166`
- tracker_sha256: `4b4b163b769e2274463bdf20c071b5f9bbae1375369c2d49edfecdac4836c271`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4096`
- audit_sha256: `9fafe2619ceb5b3b257017a832bf5fe62516eadf813879ca3edae3f102cd1663`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `22449`
- default_report_sha256: `3a0e6810cf7af536b098ae0e9662c0fb85b426f2b69b51ed4bd11e4746779282`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `24032`
- default_env_sha256: `d45cc2e9bf14199c889f25db719575209b5a6bf4f56175bb719e1e45bdbc4b45`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `2bb71fcaf53ac7ff3235cff05e55c52d71d3a3464ed476b55a47671ee9dcf83d`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `8b4788b1e7d8c7855c1254736e932ab24fffbead4d6addde4f0367c34c3c6e55`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `3719ded873e237cf1a209aad022aa54eac05cdd56767c2c21ba6402837d7f304`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
