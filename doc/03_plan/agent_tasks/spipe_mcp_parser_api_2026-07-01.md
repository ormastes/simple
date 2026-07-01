# SPipe MCP Parser API Task

## Done

- Added common `SourceBlob`, `TreeNode`, `TreeDoc`, and `ContextStore` API.
- Added parser matching for generic text/logs, file trees, and common Ubuntu
  CLI families: find, ls, tree, rg, grep, git, gcc/clang/ld, cmake, ninja,
  make, pytest, ctest, cargo, npm, journalctl, systemctl, RepoMix, Markdown.
- Added compact render output with level-first grouping when explicit levels
  exist, parent chains for mid-context snippets, and raw line pointers.
- Added `src/app/spipe_mcp/main.spl` executable commands: `parsers`, `match`,
  `parse`, and `raw`.
- Added MCP stdio mode with `initialize`, `tools/list`, and `tools/call` for
  parser list, parser match, tree parse, session-local context put/get/search,
  and raw-line retrieval.
- Added deterministic Ponytail MCP tools: `spipe_minimality_check`,
  `spipe_minimality_review`, and `spipe_minimality_debt`.
- Added hook normalization tools: `spipe_hook_event`, `spipe_hook_rules`, and
  `spipe_hook_render`.
- Added codebase-mcp compatibility ingest tools: `spipe_codebase_profile`,
  `spipe_codebase_ingest`, `spipe_codebase_search`, `spipe_codebase_get`, and
  `spipe_codebase_save` metadata.
- Added `spipe_codebase_pack` and `codebase-pack`, using the app process facade
  to run RepoMix with a fixed argv vector and ingest stdout without returning
  the whole pack through MCP.
- Added durable SQLite context tools: `spipe_context_sql_put`,
  `spipe_context_sql_get`, and `spipe_context_sql_search`.
- Added `simple spipe-mcp ...` CLI dispatch wiring for common source-mode use;
  the installed release binary needs rebuild before the shortcut is live there.
- Added focused unit coverage.

## Remaining

- Full completion audit against the broad SPipe MCP objective.

Sidecar lanes: N/A for this first common API patch.
Merge owner: Codex.
Final reviewer: normal LLM review before marking the full SPipe MCP goal done.
