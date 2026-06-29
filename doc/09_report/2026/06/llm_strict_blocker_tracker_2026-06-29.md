# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `97a84d3db1884efa4d5db369c4207260b30eec1a664087b3e9df2fa60710de53`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `645a98b7391e95c653e57f8bc421cc61ef34181832844a5edec692ed5c5db686`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `23828`
- default_report_sha256: `77ee07821587715149897cb7d0ffde54ae0fdcf256b7ce9506cfa4e60c3a287c`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `26507`
- default_env_sha256: `9fe59fd04e0940dc47731305959b49e96f6c0a313741dc9d7beee91b78c4dc9a`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `96b1de4e91491900eda4334c21c569cbaff0521125324183ef9e4ea88fa8cda8`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `93d72812ddbcd957131c6b8015722364950770a1dbc7a90cebed500a547a9604`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `311dab85bdc246967d9f81f670d060f4f7867c30a65e0b1c37cedc23153729a6`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
