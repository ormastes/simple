# File Change Provenance Query / Lint-Question Feature

**Type:** Feature
**Category:** DX / Tooling / MCP
**Priority:** High
**Proposed:** 2026-04-16
**Status:** Proposed

## Problem

When a Simple source file changes outside the user's direct edit — by a linter, formatter, MCP `simple_edit` tool call, IDE auto-format on save, pre-commit hook, or a concurrent Claude Code session — there is currently **no way to query**:

1. **What** changed (line-range diff)
2. **Who/what** caused the change (process, hook, agent, tool, user)
3. **When** (timestamp)
4. **Why** (the rule, prompt, or commit message that motivated it)

Concrete incident that prompted this request (2026-04-16): during an MCP-server fix session, an `as _sdk_find_simple_binary` import alias in `src/app/mcp/main.spl:34` was repeatedly reverted between Claude edits. Investigation found:
- Two long-running `bin/simple` processes from a prior session (PIDs 3087436, 3087437) holding `src/app/mcp/main.spl` and `src/app/simple_lsp_mcp/main.spl` open.
- A stale `.git/index.lock` blocking `jj op log`.
- Claude Code surfaced a `<system-reminder>` saying "modified, either by the user or by a linter. This change was intentional" — but offered **no provenance trail**, leaving the agent unable to reconcile its mental model with on-disk state.

The cost: ~3 round-trips of "edit → re-verify → re-edit" loops, ~10 minutes of investigation, and the agent had to commit fixes elsewhere (wrapper cache rejection) that masked the root cause instead of resolving it.

## Proposed Solution

### Three layered capabilities

#### 1. `simple why-changed <file>[:line-or-range] [--since <timestamp>]`

A new CLI subcommand that answers "what changed this file (or this line range) recently, and why?"

Output (text):
```
$ simple why-changed src/app/mcp/main.spl:34
2026-04-16T08:46:18Z  reverted "use ... as _sdk_find_simple_binary" → "use ... as _sdk_find_simple_binary"
  by:    process pid=3087437 (bin/simple src/app/mcp/main.spl)
  via:   simple_edit MCP tool, request_id=req-xyz-22
  cause: client="claude-code session=B" prompt="restore prior alias style"
  prior: 2026-04-16T08:42:01Z added by Edit tool, session=A, prompt="fix _sdk_find_simple_binary unresolved relocation"
```

JSON (`--format=json`) for tool consumption.

#### 2. Provenance log: `.simple/provenance/<rel-path>.log` (append-only NDJSON)

Every Simple-managed write (CLI `simple fix`, `simple fmt`, `simple lint --fix`, MCP `simple_edit`/`simple_multi_edit`, LSP code actions) appends an NDJSON record:
```json
{"ts":"2026-04-16T08:46:18Z","pid":3087437,"file":"src/app/mcp/main.spl","range":[34,38],"actor":"mcp:simple_edit","client":"claude-code","session":"B","reason":"prompt: restore prior alias style","prev_sha":"abc...","new_sha":"def..."}
```

External writers (IDE save, manual edit) leave **no record** — the absence is itself useful information ("we don't know who; probably user/IDE").

#### 3. `simple lint --question <file>[:line]`

A reverse-lookup: "if I run lint on this file/line, what rules would *fire*, what *fixes* would be applied, and *why*?"

```
$ simple lint --question src/app/mcp/main.spl:34
RULE: import-alias-style       fires: NO   (alias suppressed in mcp/* per .simplelintrc)
RULE: unused-extern            fires: NO
RULE: unresolved-import        fires: YES  → would suggest removing `as _sdk_find_simple_binary`
   reason: alias `_sdk_find_simple_binary` is referenced only inside `_mcp_find_simple_binary()` body
   fix:    `use std.mcp_sdk.core.shell.{find_simple_binary}` + rewrite caller
   note:   this fix has been applied 3 times in last 24h and reverted each time (see why-changed)
```

The "applied N times and reverted" hint surfaces oscillation patterns to the agent so it can stop fighting an external authority.

### MCP integration

Three new MCP tools under `simple-mcp`:
| Tool | Purpose |
|------|---------|
| `simple_why_changed` | Wraps `simple why-changed` |
| `simple_lint_question` | Wraps `simple lint --question` |
| `simple_provenance_tail` | Stream new entries from `.simple/provenance/<file>.log` |

LLM agents (Claude Code, Claude Agent SDK consumers) can call these before a re-edit to detect "this change keeps getting reverted by X — stop and ask the user."

## Implementation Notes

- **Logging hook:** Add a single `provenance_record(file, range, actor, reason)` helper in `src/lib/nogc_sync_mut/provenance/`. Wire it into:
  - `src/app/mcp/main_lazy_diag_tools.spl` (simple_edit, simple_multi_edit handlers)
  - `src/app/cli/lint_entry.spl` (fmt, fix, lint --fix)
  - `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` (code actions)
- **Log rotation:** Cap at 1 MiB per file; rotate to `.log.1`. Total provenance footprint <50 MiB for typical repo.
- **Content-addressed:** Store `prev_sha`/`new_sha` (BLAKE3) so we can reconstruct the exact text that was reverted, not just describe it.
- **External-writer detection:** Compare on-disk SHA against last-known-recorded SHA on every read; if they differ and there's no provenance record, log a synthetic `{"actor":"unknown","reason":"file modified externally"}` entry with the on-disk mtime.

## Acceptance Criteria

- [ ] `simple why-changed src/app/mcp/main.spl` returns at least one recorded change after running `simple fmt` on the file.
- [ ] `simple lint --question` outputs the "applied N times and reverted" hint when oscillation detected.
- [ ] MCP `simple_why_changed` tool surfaces the same data over JSON-RPC.
- [ ] When two concurrent sessions edit the same file, the second session's `simple why-changed` shows the first session's recent edit.
- [ ] External edits (IDE save) appear as `{"actor":"unknown"}` records.

## Why Not Just Use `git blame`?

- `git blame` shows commit-level provenance, not in-flight edits.
- `git blame` requires a commit — pre-commit hook reverts never get blamed.
- `git blame` doesn't capture the *prompt* or *rule* that motivated the change — only the commit message.
- Reverts within 1 second leave no `git` trace if uncommitted.

## Related

- `improve_request.md` — symbol_table_spec.spl improvement work (similar tooling-DX class).
- `simple_lsp_visibility_support.md` — adjacent LSP UX gap.
- `t32_mcp_cli_improvements.md` — sibling MCP DX request.

## Out of Scope

- Provenance for binary files (`.smf`, build artifacts) — track only `.spl`/`.shs`/`.sdn`.
- Cross-machine sync (provenance is local-repo only; for multi-developer use a VCS commit).
