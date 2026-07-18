# LLM Feature DB Reference Integrity

- status: `pass`
- reason: `feature_db_references_exist`
- scope: `llm_feature_db_local_paths`
- required_gates: `all_referenced_paths_exist,stale_svllm_generated_spec_paths_absent`
- blocked_gates: `none`
- primary_blocked_gate: `none`
- rows_checked: `11`
- paths_checked: `292`
- missing_count: `0`
- stale_svllm_path_count: `0`
- surface_manifest: `build/llm_feature_db_reference_integrity/feature_db_reference_surface_manifest.tsv`
- surface_manifest_count: `2`
- surface_manifest_size: `240`
- surface_manifest_sha256: `36fae1c62362179158a74e3a33eb922bf95c54bd466d9b1e2da59db4957f4dfc`
- next_action: `feature DB LLM references are current`
- env: `build/llm_feature_db_reference_integrity/evidence.env`

This evidence verifies that LLM-related feature database rows reference existing local repository paths and that the known svLLM generated-spec docs stay on their real `doc/06_spec/test/01_unit/...` locations.
