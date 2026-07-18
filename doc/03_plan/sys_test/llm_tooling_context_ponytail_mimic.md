# System Test Plan: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## Implemented Slices

Use unit specs for helper behavior, MCP source-contract coverage, and the
existing integration CLI spec for log-mode behavior.

Add or extend:

- `test/01_unit/app/tooling/context_generate_spec.spl`
- `test/unit/app/tooling/context_generate_spec.spl`
- `test/01_unit/app/tooling/ponytail_audit_spec.spl`
- `test/unit/app/tooling/ponytail_audit_spec.spl`
- `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl`
- `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl`
- `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl`

Keep:

- `test/02_integration/app/context_log_modes_spec.spl`

## Acceptance Checks

- `simple check src/app/io/context_ops.spl src/app/context/main.spl src/app/mcp/main_lazy_query_tools.spl src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl`
- `simple test test/01_unit/app/tooling/context_generate_spec.spl --mode=interpreter --clean`
- `simple test test/unit/app/tooling/context_generate_spec.spl --mode=interpreter --clean`
- `simple test test/01_unit/app/tooling/ponytail_audit_spec.spl --mode=interpreter --clean`
- `simple test test/unit/app/tooling/ponytail_audit_spec.spl --mode=interpreter --clean`
- `simple test test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter --clean`
- `simple test test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter --clean`
- `simple test test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl --mode=interpreter --clean`
- `simple test test/02_integration/app/context_log_modes_spec.spl --mode=interpreter --clean`
- `sh scripts/audit/direct-env-runtime-guard.shs --working`
- `sh scripts/audit/direct-env-runtime-guard.shs --staged`
- `sh scripts/check/check-llm-tooling-public-absence-rendering.shs`
- `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`

## Coverage Notes

- `simple_context` coverage includes local index/query, embedded SQLite
  index/query, source-less persisted SQL query, and SQL `source_filter`
  forwarding through live app MCP plus lower MCP schema/handler parity.
- `simple_ponytail` coverage includes audit and simplification report modes,
  app/lower handler mode parity, public schema exposure, JSON/Markdown/text
  rendering contracts, and absence rendering without internal absence markers.
