# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `bd19230f6f65e0bf6dc10cb5710b541af923990c4f9dbe06ca07b03a69640175`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `95f3dae6fac2ef69e43cec5cdda24927eb4c3536ea412b3c7d18fb2ab21cb161`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `29472`
- default_report_sha256: `e3fb9eeab6c298b608217e90c931ecc1feecdc39c11db47b5e5d25f3d5bceb8b`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `34736`
- default_env_sha256: `1878c0bbce76c13d0adc042d04a7c82581b023821f2e233590aaf45561c580bd`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `15`
- vllm_surface_manifest_sha256: `a4ca90b8196d0cc8fbffef4782ad993c82a7201217e0f440d0a20353b51e1075`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `19`
- torch_surface_manifest_sha256: `5769be59bbaac9c4790f3ce917804a703e3f2c3fbe48e99a36f9144c9691e77a`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `123`
- public_absence_surface_manifest_sha256: `25c0c2106b1b7565dd37cc4a05dceedba094b46071aaca5268035584f848e528`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
