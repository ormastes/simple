# LLM Tooling Context/Ponytail Mimic Evidence

- status: `pass`
- strict_full_replacement: `false`
- full_replacement: `not_required`
- full_replacement_reason: `default_local_mimic_evidence_only`
- full_replacement_env: `build/llm_tooling_context_ponytail_full_replacement/evidence.env`
- system_spec: `pass` exit=`0` log=`build/llm_tooling_context_ponytail_mimic/context_ponytail_mimic_system.log`
- context_unit: `pass` exit=`0` log=`build/llm_tooling_context_ponytail_mimic/context_generate_unit.log`
- ponytail_unit: `pass` exit=`0` log=`build/llm_tooling_context_ponytail_mimic/ponytail_audit_unit.log`
- env: `build/llm_tooling_context_ponytail_mimic/evidence.env`

This evidence covers the checked-in Simple context-mode mimic, embedded-SQL context query path, Ponytail audit surface, and MCP/guide contract assertions in the executable specs. It does not prove full context-mode fetch/index replacement beyond local file packs or full external Ponytail workflow replacement; run with `--strict-full-replacement` when that completion evidence must pass.
