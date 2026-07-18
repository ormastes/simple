# LLM Tooling Context/Ponytail Mimic Evidence

- status: `pass`
- strict_full_replacement: `false`
- full_replacement: `not_required`
- full_replacement_reason: `default_local_mimic_evidence_only`
- full_replacement_env: `build/llm_tooling_context_ponytail_full_replacement/evidence.env`
- system_spec: `pass` exit=`0` log=`build/llm_tooling_context_ponytail_mimic/context_ponytail_mimic_system.log`
- system_spec_log_size: `1431`
- system_spec_log_sha256: `98e51be0f8a1316fe561141aa7243438a5760e0883dbb25a4694f111a4c96435`
- context_unit: `pass` exit=`0` log=`build/llm_tooling_context_ponytail_mimic/context_generate_unit.log`
- context_unit_log_size: `1381`
- context_unit_log_sha256: `90b980addad5ae6cbde58993c9fdc9bcb09f844c36993892ae15bbe8b615f6c7`
- ponytail_unit: `pass` exit=`0` log=`build/llm_tooling_context_ponytail_mimic/ponytail_audit_unit.log`
- ponytail_unit_log_size: `1374`
- ponytail_unit_log_sha256: `c36605c149584c6fd1a3836936b9c9aa1b5ae180e966df65f2e5c6b8bf8703f1`
- surface_manifest: `build/llm_tooling_context_ponytail_mimic/context_ponytail_mimic_surface_manifest.tsv`
- surface_manifest_count: `10`
- surface_manifest_size: `1327`
- surface_manifest_sha256: `756ad9a3c9b385bbb8b82259d0dd5e391bb96acec3d437781f91bdffc0aee401`
- env: `build/llm_tooling_context_ponytail_mimic/evidence.env`

This evidence covers the checked-in Simple context-mode mimic, embedded-SQL context query path, Ponytail audit surface, and MCP/guide contract assertions in the executable specs. It does not prove full context-mode fetch/index replacement beyond local file packs or full external Ponytail workflow replacement; run with `--strict-full-replacement` when that completion evidence must pass.
