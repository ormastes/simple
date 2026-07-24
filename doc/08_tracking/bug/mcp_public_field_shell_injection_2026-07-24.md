# MCP public-field shell injection

**Status:** PARTIAL / FIX IN PROGRESS  
**Scope:** `src/app/mcp` source-mode server; the issue is independent of the
currently unavailable qualified native MCP artifact.

`extract_field` returns caller-controlled JSON text. Several active handlers
still concatenate it (or a direct derivative) into a command passed to
`shell_cmd`, which invokes a shell. Quoting one field is not a repair: shell
metacharacters, command substitutions, and option parsing remain reachable.

## Active residual inventory (2026-07-24)

| Scope | Public fields reaching a shell command | Evidence |
|---|---|---|
| VCS | None in the active VCS handler | All VCS handlers now pass public fields as literal arguments through `mcp_run_argv`. |
| Query | None in the active read-only query handler | Public query, file, revision, requester, and derived module values now use bounded argv or in-process scanning. Two project-summary shell pipelines remain, but their commands are constant and contain no request fields. |
| Diagnostics | `path`, `directory` | `main_lazy_diag_tools.spl`: structured check, symbols, and status fallback `find`. |
| CLI passthrough | tool-specific fields such as `path`, `filter`, `query`, `files`, `target`, `package`, `pattern` | `cli_passthrough.spl`: `_append_cli_args_for_name` appends public fields, then `handle_cli_passthrough_direct` calls `shell_cmd`. |

`main_dispatch.spl` imports the four scopes above, so they are active. The
separate legacy/core copy is `main_dispatch_core.spl`: it also concatenates
`query` and `file` into `grep`, but is not imported by `main_dispatch.spl`.
It is tracked separately; do not treat its migration as proof that active
handlers are safe.

## Root cause and bounded repair

The trust boundary is crossed at `extract_field`, then lost in text command
construction. Migrate each handler to the existing bounded argv owner
`mcp_run_argv(program, args, timeout_ms, max_output_bytes)`: one argument per
public field, with fixed program/options, explicit `--` before paths, and the
current timeout/output caps. Keep the shell only for fixed, no-public-input
commands; replace the `simple_test` wrapper with an argv/process helper rather
than quoting more strings.

The accompanying static guard proves the completed VCS/query migration and
allows only the two constant query-summary pipelines. It does **not** claim
complete MCP hardening or cover diagnostics, CLI passthrough, indirect aliases,
or legacy code.
