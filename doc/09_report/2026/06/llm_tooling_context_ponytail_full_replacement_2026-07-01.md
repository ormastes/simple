# LLM Tooling Context/Ponytail Full Replacement Evidence

- status: `pass`
- reason: `repo_local_replacement_surfaces_verified`
- scope: `repo_local_simple_owned_surfaces`
- required_gates: `mimic_evidence,execution_spec,execution_sql_dispatch,execution_public_absence_runtime,execution_live_tools_list,execution_lower_tools_list,execution_lower_context,execution_lower_ponytail,generated_execution_manual,generated_system_manual,wrapper_manifest,guide_replacement,guide_context,guide_ponytail,guide_sql,architecture_contract,architecture_no_parallel,requirements_sql,requirements_mcp,app_context_table,app_context_sql,app_context_filter,app_ponytail_table,app_context_dispatch,app_ponytail_dispatch,app_context_sourceless,app_ponytail_handler,lower_context_schema,lower_context_sql,lower_context_filter,lower_ponytail_schema,lower_context_dispatch,lower_ponytail_dispatch,lower_context_sourceless,lower_context_filter_handler,lower_ponytail_handler`
- blocked_gates: `none`
- primary_blocked_gate: `none`
- surface_check_count: `28`
- failure_count: `0`
- mimic_status: `pass`
- mimic_env: `build/llm_tooling_context_ponytail_full_replacement/mimic/evidence.env`
- mimic_env_size: `1518`
- mimic_env_sha256: `5d54ddec784af0d44ead4d615d61c84d33f92d8e1379500cf66a0765bacdb464`
- mimic_log_size: `48`
- mimic_log_sha256: `39121936f29d4d543d55c593965da75296ab8a08ba4dacf35d347126919c6b85`
- execution_spec_status: `pass`
- execution_sql_dispatch_status: `pass`
- execution_public_absence_runtime_status: `pass`
- execution_live_tools_list_status: `pass`
- execution_lower_tools_list_status: `pass`
- execution_lower_context_status: `pass`
- execution_lower_ponytail_status: `pass`
- execution_spec_log: `build/llm_tooling_context_ponytail_full_replacement/mcp_context_ponytail_dispatch_spec.log`
- execution_spec_log_size: `1458`
- execution_spec_log_sha256: `ead3b4875816fe131fa338faa957a0e740fac20734ef777ca2361fef1ec3bc06`
- surface_manifest: `build/llm_tooling_context_ponytail_full_replacement/replacement_surface_manifest.tsv`
- surface_manifest_count: `15`
- surface_manifest_size: `1901`
- surface_manifest_sha256: `4267f270a81ddf71902a2f27f25a0f99902636d6a1ac8d9f6b859624af5585a1`
- failures: `none`
- next_action: `strict context/Ponytail full-replacement evidence is ready`
- env: `build/llm_tooling_context_ponytail_full_replacement/evidence.env`

This evidence proves the checked-in operator, CLI, app MCP, lower MCP, dashboard-adjacent, embedded-SQL, and Ponytail surfaces converge on Simple-owned `simple_context` and `simple_ponytail` contracts, and runs an execution spec that calls file context, source-less embedded-SQL context, and Ponytail through the app MCP dispatcher. It is repo-local replacement evidence; it does not claim internet fetch, external vector store, or third-party plugin parity.
