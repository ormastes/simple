# MCP progressive hints: pure policy landed, MCP wiring and stale-hint CI missing

- Date: 2026-11-14
- Status: open
- Area: MCP (`src/app/mcp/**`), LLM policy (`src/lib/common/llm/`)
- Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` §7, §9 (HINT-001..010)
- Feature expert: `doc/00_llm_process/feature_expert/mcp_progressive_hints/skill.md`

## What exists

`src/lib/common/llm/hint_policy.spl` — pure `decide_hint(state, event, now, version)
-> (HintLevel, HintState)` covering HINT-001..008, spec
`test/01_unit/lib/common/llm/hint_policy_spec.spl` (10 examples). Nothing calls it yet.

## What remains

1. **DONE 2026-11-15 (slice mcphints, PR on release/1.0.0)** — **MCP tools** (plan §7.1): `simple_help(topic?, level=brief|full, examples?)`,
   `simple_capabilities(category?, goal?, platform?)`, `simple_hint_status(topic?)`.
   Registered in `src/app/mcp/main_lazy_hint_tools.spl`; per-session map in `main_session_state.spl`. NOT done within this item: appending hints to other tools' responses on the response path (needs a typed error kind on `ToolFailed`; no other tool calls `decide_hint` yet). Original gap: None are registered in `src/app/mcp/`. Unblock: a serialized MCP-wiring slice that
   owns a per-session `HintState` map keyed by session x capability x version and
   calls `decide_hint` from the response path (hints appended, never replacing errors).
2. **MCP resources**: `simple://guide/quickstart`, `simple://capabilities/traceability`,
   `simple://capabilities/testing`, `simple://capabilities/debug`,
   `simple://skills/catalog`. Not served.
3. **MCP prompts**: `simple-onboard`, `simple-debug`, `simple-verify`. Not served.
4. **HINT-009 (DONE for the three new tools' hint text; spec `mcp_hint_tools_spec.spl`)** — every hint text references an actually registered command/tool.
   Needs hint text (none exists yet) plus a check against the MCP tool registry.
5. **HINT-010** — CI catches stale hints after a command/tool rename. Unblock: item 4
   plus a `scripts/check/` gate wired into the extended CI job.
6. **Provider hooks** (plan §7.2): extend the Claude `grep_hint` /
   `read_analysis_hint` / `bash_output_hint` templates; Codex/Gemini/Kimi adapters.

## Policy approximations to revisit (not defects in the pure slice)

- `hint_policy.spl` `_hint_inactive_long`: "30 days of inactivity" is measured from
  `last_hint_time`, because the plan's six-field state has no last-use time. An
  actively used capability therefore re-hints once every 30 days. Unblock: owner
  decision to add a `last_used_time` field.
- `hint_policy.spl` `_hint_errors_within_window`: "3 matching errors" counts all
  failures of the capability; error identity is not modelled. Unblock: the wiring
  slice supplies a typed error kind on `HintEvent.ToolFailed`.
- Thresholds (600 s, 3, 5, 30 days) are the plan's initial NFR targets, not
  telemetry-tuned values.

## Slice mcphints status (2026-11-15)

Done: part 1 (tools, per-session map, spec). NOT done, still open: resources
`simple://guide/quickstart`, `simple://capabilities/<name>`, `simple://skills/catalog`
and prompts `simple-onboard|debug|verify` (items 2-3 above); removal of the 3
`primitive_api` findings in `src/app/mcp/main_lazy_ctx_tools.spl` (`timeout_ms` on
`ctx_run_bounded`/`ctx_execute_code`, `cap` on `ctx_smart_truncate`; callers include
`test/01_unit/app/mcp/ctx_capture_truncation_spec.spl:122` and
`test/03_system/app/mcp/feature/mcp_token_reduction_spec.spl:49,91`); HINT-010; provider hooks.
`ctx_tools_spec.spl` is flaky under host load ("Process timed out" in shell-spawn
examples): 25/25 idle, 21-24/25 under load, including on the base tree.
