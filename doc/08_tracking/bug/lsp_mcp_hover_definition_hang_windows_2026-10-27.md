# simple-lsp-mcp: lsp_hover / lsp_definition never respond on Windows

- **Status:** open. **Owner:** src/app/simple_lsp_mcp (LSP query path).
- **Symptom:** `lsp_hover` and `lsp_definition` were called on test/01_unit/language/accessor_forwarding/probe_setter.spl (line 27 char 30 `t.celsius`, line 29 char 7) and probe_alias.spl (line 29 char 30 `h.greet`). None of the calls returned; each hit the client's 1800 s idle timeout. `lsp_visibility` on the same server returned within seconds earlier in the same session.
- **Impact:** the planned LSP checks for forwarded getters, setters and aliased trait methods (hover/definition should resolve to get_x/set_x or to the field's trait method) cannot run. That coverage is tracked as PR5 in doc/03_plan/compiler/selfhost_accessor_forwarding_pr_series_plan.md.
- **Next step:** run the underlying `query_visibility.spl hover` / definition subprocess by hand with a timeout. That will show whether the child process hangs or the MCP response is lost.
