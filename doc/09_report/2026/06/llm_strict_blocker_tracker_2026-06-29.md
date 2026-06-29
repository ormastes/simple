# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `29`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `4663`
- tracker_sha256: `c5f850e5adcfeb96862cfb9863174205284d1b182d0f9245ff893f7393805054`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3295`
- audit_sha256: `6e79374334be6fe69fe632c6f01b5f8b6bd226c61859ef9417aadcd3c3cecb56`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `15811`
- default_report_sha256: `7164e07377ad34d7401f6010fe2380ba187438a86de678590d888a0d30ad8a74`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `16957`
- default_env_sha256: `885f1a75beee3e943632d175fa289285629953cec0eb5278dababa23977bcb32`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `10`
- vllm_surface_manifest_sha256: `83abdc5c0a155eb8bc2cd2c20e3a9349d0e5b43cacf1073c5d59706b5fe9500b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `14`
- torch_surface_manifest_sha256: `852a1c814199286c0cf686f2bc68ffc8fb946a85691426a4c7440cf69aa7165c`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch provenance counts and hashes.
