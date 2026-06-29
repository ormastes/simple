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
- mimic_env_size: `569`
- mimic_env_sha256: `397003f765af393e58903e1ceb076dd294cbd8d80f67e42f3ed8d1b12b5b011a`
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
- execution_spec_log_sha256: `f38b9cc796ae35dc7fb14cfa1bbd704e6ba46558600e7b25c9da1877aa55b23e`
- surface_manifest: `build/llm_tooling_context_ponytail_full_replacement/replacement_surface_manifest.tsv`
- surface_manifest_count: `15`
- surface_manifest_size: `1901`
- surface_manifest_sha256: `0a922de9859a2224c04272830af9a4be03a86780452ffabdde38523e5238f0ab`
- failures: `none`
- next_action: `strict context/Ponytail full-replacement evidence is ready`
- env: `build/llm_tooling_context_ponytail_full_replacement/evidence.env`

This evidence proves the checked-in operator, CLI, app MCP, lower MCP, dashboard-adjacent, embedded-SQL, and Ponytail surfaces converge on Simple-owned `simple_context` and `simple_ponytail` contracts, and runs an execution spec that calls file context, source-less embedded-SQL context, and Ponytail through the app MCP dispatcher. It is repo-local replacement evidence; it does not claim internet fetch, external vector store, or third-party plugin parity.
