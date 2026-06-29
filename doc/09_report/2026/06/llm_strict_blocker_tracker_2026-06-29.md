# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6132`
- tracker_sha256: `c6a113c6c74edf3c2a36e30a63c50dbcaa21021059d684f8dd6fcc2e9dcbdf28`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4062`
- audit_sha256: `a6f02d2736246faa65e1dff5e347229a30e510540017b77531d90cd618a350c3`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `20131`
- default_report_sha256: `f80288f8fc208ad101ee525ec9a43957291f3bffab4130ab8fb3336738361397`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `21791`
- default_env_sha256: `690447e5b651303781340533c841415f05c13e3339ed920b2acea4afc1c54b5a`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `c514ad1e0b8c408dd29d4c10e687650cf01179215fd9dd9a45f4d30bc74dba8f`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `4efc29a41912b80f97b02dbae6182184ccd042b0d8951f516f68bbe24291b933`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `121`
- public_absence_surface_manifest_sha256: `93c3ae4d224b8a6e8d535238870cedc0bba2c02b887570980c695a778f926e87`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
