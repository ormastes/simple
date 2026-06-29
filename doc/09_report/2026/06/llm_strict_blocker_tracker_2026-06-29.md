# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `5261`
- tracker_sha256: `378e210393e6652347729b43e96c800400dde8e66cd86265ba1337c0f8c24616`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3643`
- audit_sha256: `6ccc79726fc6387f1ddf86d88457cbb8c78263720cb3df83536854d82c06344e`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `16008`
- default_report_sha256: `2b5a6b7e53a649ac33e08c6b3138bead358a740c574630241b3504057b766c87`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `17720`
- default_env_sha256: `c3f2eb7afb6404888232c3deda64fe3f317886978ea6c75e163bf76896af6093`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `10`
- vllm_surface_manifest_sha256: `83abdc5c0a155eb8bc2cd2c20e3a9349d0e5b43cacf1073c5d59706b5fe9500b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `14`
- torch_surface_manifest_sha256: `852a1c814199286c0cf686f2bc68ffc8fb946a85691426a4c7440cf69aa7165c`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `93`
- public_absence_surface_manifest_sha256: `564c57ce69260d0dbd96a5f6995f123de0a3b14024831464ec60cfbd2551282f`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
