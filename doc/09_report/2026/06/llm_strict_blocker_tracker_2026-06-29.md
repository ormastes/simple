# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `36`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `5818`
- tracker_sha256: `a369ceced70e3c52eb3ff3bb5f8840e676ecfd9279b0ded3997bf2fc7d90d263`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `3890`
- audit_sha256: `b45b2959e8baa5d0e10f68c97f4177838b4077c5315d3b659c2f140e3873808c`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `17981`
- default_report_sha256: `9a4a5db2226eec0c4628fab20c7d7ceefbfc0b52455f769f49d5ebc099f93d05`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `19693`
- default_env_sha256: `49e7774ebc6efbb5a1779f0cd72d95df63b8ba5ce441eae327954dee829b0616`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `35c47029787ab6a878e1c2b9e5bc6789a40eaf44c5573b385bc5d9144729325d`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `dd7796837a328390a24abdd5d2769f8d3dafcdaedca0d840f3adc73f1dbbdef3`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `93`
- public_absence_surface_manifest_sha256: `6f4cfecd1df9d67a6249a072e9bd8bac4ac3622e8a136e3176ce92aab9cd7c3c`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
