# Recent Bugs

**Generated:** 2026-04-14
**Database:** `doc/08_tracking/bug/bug_db.sdn`
**Open:** 0 | **Closed:** 24

## Open Bugs

No open bugs.

## Closed Bugs

| ID | Severity | Status | Title |
|----|----------|--------|-------|
| bootstrap_001 | P0 | invalid | MIR lowering receives 0 HIR modules [OUTDATED] |
| bootstrap_002 | P1 | invalid | Bootstrap compilation extremely slow [OUTDATED] |
| dict_semantics_001 | P3 | closed | Dictionary mutation suspected issue [RESOLVED] |
| string_001 | P0 | invalid | Missing string method trim_start_matches [OUTDATED] |
| parser_001 | P1 | invalid | Parser rejects slice reference syntax &[T] [OUTDATED] |
| parser_002 | P2 | invalid | Parser rejects if-then syntax [OUTDATED] |
| cli_001 | P1 | invalid | Method mutability errors in CLI parser [OUTDATED] |
| mcp_jj_001 | P2 | cannot_reproduce | MCP jj tool (mcp__simple-mcp-jj) may hang or be unreliable |
| test_runner_slow_001 | P3 | fixed | Test runner startup takes 56 seconds for single-file mode |
| cli_bug_add_001 | P2 | fixed | bin/simple bug-add command fails with LOG_ERROR not found |
| fileio_lite_safe_read_001 | P2 | closed | fileio_lite safe_read crashes: text iteration + Option unwrap |
| simple_mcp_null_param_001 | P2 | closed | simple-mcp: JSON null param treated as literal string 'null' |
| simple_mcp_parse_error_001 | P2 | closed | simple-mcp: malformed JSON silently dropped, no parse error response |
| simple_mcp_no_id_001 | P3 | closed | simple-mcp: request without id produces invalid JSON response (id:,) |
| mcp_jj_commit_001 | P2 | fixed | MCP jj_commit silently fails: message not shell-quoted, multi-line breaks shell |
| use_lazy_parse_001 | P1 | fixed | use lazy X.{Y} syntax not supported by runtime Rust parser |
| mcp_di_nil_handler_001 | P2 | fixed | dispatch_tool crashes on nil handler if di_resolve fails |
| mcp_di_debuglog_error_001 | P2 | fixed | debuglog resource returns plain text error as application/json |
| mcp_di_config_path_001 | P3 | fixed | init_di uses relative path config/di.sdn, fails silently from wrong cwd |
| mcp_wrapper_entrypoint_001 | P2 | fixed | MCP wrapper scripts referenced missing src/app/mcp/main_lite.spl |
| mcp_codex_handshake_001 | P1 | closed | simple-fileio and jj-git-mcp fail Codex MCP initialize handshake |
| simple_mcp_check_cmd_001 | P1 | closed | main_lazy simple_check pipeline calls unsupported 'bin/simple check' command |
| simple_mcp_multi_edit_001 | P2 | closed | main_lazy simple_multi_edit does not apply provided edits payload |
| parser_004 | P2 | closed | Try operator (?) in for loops - FALSE BUG |
