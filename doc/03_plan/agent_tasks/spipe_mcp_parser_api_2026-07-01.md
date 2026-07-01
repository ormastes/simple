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
- Added focused unit coverage.

## Remaining

- Add durable SQL/FTS storage for context-mode retrieval.
- Add RepoMix/codebase pack execution using argv-safe process APIs; current
  code ingests existing packed text and rejects shell metacharacters in pattern
  arguments.

Sidecar lanes: N/A for this first common API patch.
Merge owner: Codex.
Final reviewer: normal LLM review before marking the full SPipe MCP goal done.
