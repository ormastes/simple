# LLM Strict Blocker Tracker Consistency

- status: `pass`
- reason: `tracker_consistent`
- checked_count: `44`
- tracker: `doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`
- tracker_size: `6387`
- tracker_sha256: `07b94b81bb64b4e6f8ccae0fafa6c90a1e75b4d185adbd43a416e7d3ab12faae`
- audit: `doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`
- audit_size: `4317`
- audit_sha256: `b3cd56bc415ca4eb32912d46b1072e670d0d1d867fd1b38e40a0cc8a5ad7c593`
- default_report: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- default_report_size: `25024`
- default_report_sha256: `c371d386f292f9e2e4b11825766b37e0f8954ea2ae7a344082740027969c163c`
- default_env: `build/llm_goal_evidence/evidence.env`
- default_env_size: `27874`
- default_env_sha256: `628a1243b017c31ac7064ff509008c53681330f5cf58179619edc91697f29ecc`
- default_warn_source: `doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`
- vllm_detail_source: `build/llm_goal_evidence/evidence.env`
- vllm_surface_manifest_count: `13`
- vllm_surface_manifest_sha256: `fc771779a44b610ff3e5cce68fd954579e3150272e3ced56b44314d79245ae58`
- torch_detail_source: `build/llm_goal_evidence/evidence.env`
- torch_surface_manifest_count: `18`
- torch_surface_manifest_sha256: `e8d9a4afb2c69533d7f0e0f84e9b03acd6b04eaae6a5cda8097ce62914ac048b`
- public_absence_detail_source: `build/llm_goal_evidence/evidence.env`
- public_absence_surface_manifest_count: `122`
- public_absence_surface_manifest_sha256: `b9396db57c7af38766e8f939581b116203e4f020535929b2fd5515e0a982d518`
- public_absence_failure_count: `0`
- env: `build/llm_strict_blocker_tracker/evidence.env`

This guard keeps the strict-host blocker tracker aligned with the latest default aggregate evidence and strict completion audit. It requires the aggregate Markdown report to match when that report exists; while the report is absent during regeneration, it accepts the aggregate evidence env as the source for default warn gates. It does not run live host evidence; it fails when the committed tracker/audit no longer name the known strict blockers or the current aggregate vLLM/Torch/public-absence provenance counts and hashes.
