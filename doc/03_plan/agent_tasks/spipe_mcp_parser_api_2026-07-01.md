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

## Acceptance Evidence

Design source:
`doc/01_research/infra/tooling/spipe_mcp_design_2026-07-01.md`.

| AC | Status | Evidence |
|----|--------|----------|
| 1. `initialize` succeeds | done | `scripts/smoke/spipe_mcp_protocol_smoke.spl` asserts `"protocolVersion"`. |
| 2. `tools/list` returns spipe tools | done | Smoke asserts `"spipe_context_put"` appears in `tools/list`. |
| 3. `tools/call` `spipe_context_put` succeeds | done | Smoke asserts `stored exec:smoke`. |
| 4. `tools/call` `spipe_context_search` succeeds | done | Smoke searches `bad` and asserts rendered tree content. |
| 5. No stdout banner or non-MCP stdout | done | `require_jsonrpc_stdout` rejects any non-JSON-RPC stdout line; error-path call is included. |
| 6. Stderr logging works | done | Smoke asserts compiler/runtime diagnostics stay on stderr via `WARN`, while stdout stays JSON-RPC only. |
| 7. Explicit log-level output groups by level | done | Smoke asserts `@group level=ERROR count=1`. |
| 8. No-level output skips level grouping | done | Smoke runs an isolated no-level parse and asserts no `@group level=`. |
| 9. Mixed output has `level=none` group | done | Smoke mixed input asserts the no-level line through the rendered tree; unit tests assert `@group level=NONE count=1`. |
| 10. Every rendered node has raw pointer | done | Smoke asserts `raw=raw:exec:smoke#L1-L1`; unit coverage checks parser nodes. |
| 11. `spipe_context_raw` returns exact original lines | done | Smoke asserts raw range and exact `[ERROR] ...` line. |
| 12. RepoMix/codebase-mcp output can be ingested | done | Smoke ingests RepoMix Markdown and asserts `repomix_markdown` plus file nodes. |
| 13. Focused Simple MCP include profile works | done | `test/01_unit/lib/nogc_sync_mut/spipe/codebase_ingest_spec.spl` asserts profile include/ignore content. |
| 14. Unsafe repo/include/ignore shell characters rejected or argv-safe | done | Smoke asserts unsafe `getCodebase` root is rejected; unit tests cover pattern validation. |
| 15. Minimality check returns delete/stdlib/native/yagni/shrink findings | done | `test/01_unit/lib/nogc_sync_mut/spipe/minimality_spec.spl` covers all listed rungs; smoke covers live native-date path. |

Additional live protocol evidence now covers SQL context put/get/search,
codebase `saveCodebase`, hook normalization, and JSON-RPC unknown-method error
responses through the same stdio oracle.

## Remaining

- Full completion audit against the broad SPipe MCP objective before marking
  the overall goal done.
- Rebuild/deploy the installed release shortcut when the broader lane moves
  from source-mode evidence to release packaging.

Sidecar lanes: N/A for this first common API patch.
Merge owner: Codex.
Final reviewer: normal LLM review before marking the full SPipe MCP goal done.
