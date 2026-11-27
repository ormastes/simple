# Feature Expert: MCP trace tools (`simple_trace`, `simple_test_query`)

## Where
- Tools: `src/app/mcp/main_lazy_trace_tools.spl` (lazy module; backends imported inside the run functions).
- Registration: `main_static_tools.spl` (descriptors), `main_dispatch.spl` (`_is_in_process_tool`, `_dispatch_ip_trace`).
- Spec: `test/01_unit/app/mcp/trace_tools_spec.spl`.
- Guide: `doc/07_guide/app/mcp/mcp.md` (tool table).

## Contract
- Read-only. `simple_trace` builds the snapshot in memory exactly like `simple trace missing` (`app.traceability.query_snapshot_v1`) and renders with `trace_query_render_missing_v1`. `simple_test_query` calls `RunnerTestDb.query_case_attempts` and refuses to load when `doc/08_tracking/test/test_db.sdn` is absent (the loader would cold-start a database).
- Required args: `profile` (a `TraceProfile` name) for trace; `path` and `name` for test query, unless `bug` or `requirement` (+ `levels`) scopes it instead. Bad args are tool errors (-32602), parsed by pure public functions over `TraceToolBody`.
- Incomplete snapshot or graph -> `status: incomplete`, `exit_code: 2`, `isError: true`.

## Known gaps
- `profile` is validated and echoed but does not yet change enforcement; only `operation: missing` exists.
- The CLI `simple trace missing` returns 1 for an incomplete graph; the tool reports 2 per plan section 6.4.
