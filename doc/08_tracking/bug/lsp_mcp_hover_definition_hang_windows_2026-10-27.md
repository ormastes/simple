# simple-lsp-mcp: lsp_hover / lsp_definition never respond on Windows

- **Status:** open. **Owner:** src/app/simple_lsp_mcp (LSP query path).
- **Symptom:** `lsp_hover` and `lsp_definition` were called on test/01_unit/language/accessor_forwarding/probe_setter.spl (line 27 char 30 `t.celsius`, line 29 char 7) and probe_alias.spl (line 29 char 30 `h.greet`). None of the calls returned; each hit the client's 1800 s idle timeout. `lsp_visibility` on the same server returned within seconds earlier in the same session.
- **Impact:** the planned LSP checks for forwarded getters, setters and aliased trait methods (hover/definition should resolve to get_x/set_x or to the field's trait method) cannot run. That coverage is tracked as PR5 in doc/03_plan/compiler/selfhost_accessor_forwarding_pr_series_plan.md.
- **Next step:** run the underlying `query_visibility.spl hover` / definition subprocess by hand with a timeout. That will show whether the child process hangs or the MCP response is lost.

## Observed points

1. Hover returns the enclosing call's visibility, not the forwarded signature: `lsp_hover` on probe_alias.spl (`h.greet`, line 30 col 31 1-based) answered `print("CASE forwarded={h.greet(...)}...")` with `Visibility: **private**`, i.e. the enclosing `print` call line, not the forwarded method's signature. Still open (separate from the hang; query_visibility.spl symbol-at resolution).
2. The server stays hung after one hung definition request: the stdio loop is single-threaded, so one request that never returns blocks every later request (hover included).

## Resolution

- Root cause: `clean_command_output` in src/app/simple_lsp_mcp/json_helpers.spl (old lines 348-349) stripped trailing newlines with `while joined.ends_with("\n"): joined = _slice_text(joined, 0, joined.len() - 1)`. `text.len()` counts bytes, `_slice_text` counts characters. The definition child prints `[search truncated: ... — part of the tree was NOT searched]` (em dash, multibyte), so the slice never shrank the string: an infinite loop in the server process itself (the child exited normally in about 9 s). No subprocess timeout can preempt it.
- Fix (a): `_trim_trailing_newlines` pops trailing `"\n"` by character.
- Fix (b): `run_command_text` (tools.spl) maps a `process_run_bounded` timeout (10000 ms) to `lsp request timed out after N ms`, and `position_result` turns that into a JSON-RPC error (-32001), so the loop keeps serving.
- Spec: test/01_unit/app/simple_lsp_mcp/lsp_definition_bounded_spec.spl (REQ-LSP-BOUNDED-001). Before: child-timeout at 120 s budget (red). After: 3/3.
