# MCP core-default + dynload upgrade plan (2026-06-13)

**Goal:** `core` tool set is the default advertisement, remaining tools dynload
via MCP `notifications/tools/list_changed`, full set stays choosable.

**Prior work:** `mcp_startup_perf_small_tasks_2026-06-12.md` (T1-T4 landed).
Measured: handshake `all` = 1.50 s, `core` = 0.067 s. The 1.4 s is native
rt-call overhead building the static 38 KB tools JSON (see
`doc/08_tracking/bug/rt_string_concat_quadratic_2026-06-12.md`).

## Contract (binding for all tasks)

Tool-set names (env `SIMPLE_MCP_TOOL_SET` / flag `--tool-set=`):

| Set | Default? | First tools/list | list_changed emitted? | Later tools/list |
|-----|----------|------------------|----------------------|------------------|
| `auto` | YES (new default) | core (20 tools) | yes, once, after the response | full (151, cached) |
| `all`  | choosable | full (151, cached) | no | full (cached) |
| `core` | choosable | core | no | core (strict small surface) |

Rules:
- Invalid set values fall back to `auto` (the default).
- `initialize` response declares `"tools":{"listChanged":true}` capability in
  `auto` mode only (`all`/`core` are static lists → `false`/omitted).
- Notification framing: standard `Content-Length` framed
  `{"jsonrpc":"2.0","method":"notifications/tools/list_changed"}`, written
  AFTER the first tools/list response is flushed.
- Dispatch stays UNFILTERED in every mode (stale-client safety, already
  documented in `main_dispatch.spl`).
- Full-list JSON is built ONCE per process and cached in a module-level `var`
  in `main_static_tools.spl` (`_mcp_static_tools_result_cached()`); every
  full-list serve path uses the cached accessor.

State in `main.spl`: `_MCP_TOOL_SET` (default "auto") + `_MCP_LIST_UPGRADED`
(bool, set true when the first auto-mode tools/list is served).

## Tasks (model-tagged, disjoint file scopes)

| ID | Task | Files (exclusive scope) | Model |
|----|------|------------------------|-------|
| A | Server state machine: default `auto`, listChanged capability, core-first serve, one-shot list_changed emit, upgraded→cached full | `src/app/mcp/main.spl` | sonnet |
| B | Full-list cache: module-level cache var + `_mcp_static_tools_result_cached()`; extend perf spec with cache oracle (same string object/equal + exact 151 count both calls) | `src/app/mcp/main_static_tools.spl`, `test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl` | sonnet |
| C | Specs: update tool_set spec for new default `auto` + invalid→auto; new upgrade-flow spec (auto: first=20 core, upgraded flag flips, second=151; all: first=151; core: never upgrades) | `test/01_unit/app/mcp/mcp_tool_set_spec.spl`, `test/01_unit/app/mcp/mcp_dynload_upgrade_spec.spl` (new) | sonnet |
| D | Docs: guide section "core-default + dynload" in startup guide; append plan/spipe state | `doc/07_guide/app/mcp/startup_performance.md` | haiku |
| E | Rebuild mcp-package native binary, re-measure all three sets, wrapper probe check | build + measure | orchestrator |
| R | Review all diffs vs this contract; false-green audit on specs | — | opus |

Parallelism: A, B, C, D run concurrently (disjoint files; C codes against the
contract above, not against A's WIP). E and R follow.

## Risks

- Native env_get P1 (`doc/08_tracking/bug/native_env_get_raw_pointer_2026-06-12.md`):
  env-var selection stays dead in native until fixed; flag + default cover it.
- Clients ignoring list_changed stay on core advertisement — acceptable
  (calls still dispatch; full list available on any later tools/list).
- Interpreter spec runs cannot exercise stdout framing; the upgrade-flow spec
  asserts the state machine + JSON payloads, E verifies framing end-to-end.
