# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `29`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `4604`
- tracker_sha256: `8d3f6acbe424c2c146fd1523fb9e62c4027c680c82b05435194771f448188703`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3230`
- audit_sha256: `b6618e54050f354ef73a2898aa08210f12c09e19b8d814c0595f671a4d462584`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `15773`
- default_report_sha256: `fa4c19c7578ad86246c282f6f046b100c349bc97e38562639d91193a04ae7083`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `16919`
- default_env_sha256: `b4b2b578479702feff9913f0a91595c42ca911d4f1ff5511c9303ce3c1ded1cd`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `10`
- vllm_surface_manifest_sha256: `83abdc5c0a155eb8bc2cd2c20e3a9349d0e5b43cacf1073c5d59706b5fe9500b`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `14`
- torch_surface_manifest_sha256: `852a1c814199286c0cf686f2bc68ffc8fb946a85691426a4c7440cf69aa7165c`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch provenance counts and hashes.
