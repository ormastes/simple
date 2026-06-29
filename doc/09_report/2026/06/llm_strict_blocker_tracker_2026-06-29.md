# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `29`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `4928`
- tracker_sha256: `d91f987baa279e23545e13ad8e886dc9a02c9747df27b9a1539c2082fadaa9b8`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3295`
- audit_sha256: `6e79374334be6fe69fe632c6f01b5f8b6bd226c61859ef9417aadcd3c3cecb56`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `15979`
- default_report_sha256: `d36b35d9ce861c6bb86d023d06f0c885dfc308af222b5341f55fd596fc4bd604`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `17125`
- default_env_sha256: `39dd6a52fb42e3a4cccd9b93c0dbc6f837fff0d8bfa2c11c88232eabac840fce`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `10`
- vllm_surface_manifest_sha256: `83abdc5c0a155eb8bc2cd2c20e3a9349d0e5b43cacf1073c5d59706b5fe9500b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `14`
- torch_surface_manifest_sha256: `852a1c814199286c0cf686f2bc68ffc8fb946a85691426a4c7440cf69aa7165c`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch provenance counts and hashes.
