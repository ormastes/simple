# SPipe MCP Parser API

`std.nogc_sync_mut.spipe.tree_context` is the common language-neutral parser
surface for SPipe MCP, context-mode style storage, and CLI-tool output parsing.

## API

- `spipe_source_blob(id, kind, command, raw_text)` creates raw context.
- `spipe_match_parser(kind, command, raw_text)` returns the best parser name.
- `spipe_parse_source(source)` and `spipe_parse_text(kind, command, raw_text)`
  build a `TreeDoc`.
- `spipe_render_tree(doc)` renders compact `@ctx`, `@parent`, `@node`, and
  `raw:<source>#Lx-Ly` pointers.
- `spipe_context_store_new`, `spipe_context_put`, `spipe_context_get`,
  `spipe_context_search`, and `spipe_context_raw` provide the minimal store and
  exact raw-line retrieval API.

Log levels are grouped only when explicit levels are detected. Plain output
renders in tree/path order with `level_detected=false`.

## CLI

```bash
bin/release/simple run src/app/spipe_mcp/main.spl
bin/release/simple run src/app/spipe_mcp/main.spl serve
bin/release/simple run src/app/spipe_mcp/main.spl parsers
bin/release/simple run src/app/spipe_mcp/main.spl match --command='git diff' -f output.txt
bin/release/simple run src/app/spipe_mcp/main.spl parse --command='simple build' -f output.txt
bin/release/simple run src/app/spipe_mcp/main.spl raw -f output.txt --start=10 --end=12 --before=2 --after=2
bin/release/simple run src/app/spipe_mcp/main.spl codebase-profile
bin/release/simple run src/app/spipe_mcp/main.spl codebase-pack --root=. --include=src/app/spipe_mcp/main.spl --ignore='.git/**,build/**'
bin/release/simple run src/app/cli/main.spl spipe-mcp parsers
```

No args and `serve` run the MCP stdio server. Logs must stay off stdout.
After the release binary is rebuilt, `simple spipe-mcp ...` is the canonical
shortcut for the same app entrypoint.

## MCP Tools

- `spipe_tree_parser_list`
- `spipe_tree_match_parser`
- `spipe_tree_parse`
- `spipe_context_put`
- `spipe_context_get`
- `spipe_context_search`
- `spipe_context_raw`
- `spipe_context_sql_put`
- `spipe_context_sql_get`
- `spipe_context_sql_search`
- `spipe_minimality_check`
- `spipe_minimality_review`
- `spipe_minimality_debt`
- `spipe_hook_event`
- `spipe_hook_rules`
- `spipe_hook_render`
- `spipe_codebase_profile`
- `spipe_codebase_pack`
- `spipe_codebase_ingest`
- `spipe_codebase_search`
- `spipe_codebase_get`
- `spipe_codebase_save`

The minimality tools are deterministic Ponytail gates. They flag obvious
`yagni`, `native`, `stdlib`, `dependency`, and `shrink` cases and list
`ponytail:` debt markers. They do not replace normal LLM review.

The hook tools normalize Claude, Codex, Gemini, and generic provider event
names into SPipe phases such as `pre_tool`, `post_tool`, `pre_prompt`,
`post_turn`, `post_edit`, and `pre_commit`.

The codebase tools run RepoMix with a fixed argv vector
`npx -y repomix <root> --stdout --style markdown --include <patterns> --ignore
<patterns>`, ingest existing RepoMix/codebase-mcp output, index it in the
session-local tree store, and expose the focused Simple MCP include/ignore
profile. `spipe_codebase_pack` returns status and byte count only; use
`spipe_codebase_search` or `spipe_codebase_get` to inspect the stored tree.
Existing XML RepoMix input with `<file path=...>` is matched as
`repomix_xml`; markdown-style packs use `repomix_markdown`.
Plain markdown sources or heading-shaped text use `markdown_headings`.
`tree` command output keeps a small path stack so nested entries render parent
directories such as `src/app` instead of isolated leaf names; rows with deeper
children are classified as directories even when `tree` omits trailing slashes.
`find` and plain file-tree output classify a path as a directory when later
rows have that path as their parent prefix.
`ls -l` output extracts ordinary entry names from permission rows and marks
rows starting with `d` as directories.
`git status` output extracts standard status paths including modified, new,
deleted, renamed, and both-modified rows.
`git diff` output extracts the destination path from `diff --git a/... b/...`
headers.
`git log --name-only` style output extracts standalone path rows.
`pytest` output extracts paths from `FAILED path::test` and `ERROR path::test`
summary rows.
`cargo` output extracts Rust diagnostic locations from `--> path:line:col`.
`npm` output extracts simple Node stack rows such as `at path:line:col`.
`cmake` output extracts file paths from `CMake Error/Warning at path:line`.
Path leaves render as `kind=file`; non-path output remains `kind=line` and can
still be grouped by explicit log level.

The SQL context tools persist the rendered parent-chain tree into the existing
Simple context SQLite table. Use `spipe_context_sql_put` with `db_path` to save
parsed output, `spipe_context_sql_get` to retrieve one source, and
`spipe_context_sql_search` to search stored parsed context by query and optional
source filter.

`spipe_context_raw` prepends the matching `@parent` chain before exact raw
lines, so a middle slice still carries command and file/dir context. If callers
pass raw text directly, SPipe parses that text first and renders the same parent
context.

## Current Boundary

This patch adds the common parser/store API, executable wrapper, minimal MCP
stdio server, deterministic Ponytail minimality tools, and hook normalization.
It also ingests existing RepoMix/codebase-mcp output and can persist parsed
context through the existing SQLite context database. RepoMix execution stays
behind the app-owned process facade and uses argv-safe arguments instead of a
shell command string.
