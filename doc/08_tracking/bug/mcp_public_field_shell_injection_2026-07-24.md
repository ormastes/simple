# MCP public-field shell injection

**Status:** FIXED IN SOURCE / STAGE 4 QUALIFICATION PENDING
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
| Diagnostics | None in the active diagnostics handler | Check, symbols, status fallback, and API search use bounded argv. Option-like status directories are rejected before `find`. |
| CLI passthrough | None | Fixed table commands and public fields use bounded argv. Positional values that could be parsed as child options are rejected; flag values remain literal argv elements. |

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

The focused VCS/query, diagnostics, and CLI-passthrough regressions cover the
active handlers. Constant, no-public-input shell pipelines remain allowed.
`main_dispatch_core.spl` is an inactive legacy copy and remains separately
tracked; a fresh Stage 4 native MCP handshake is still required before runtime
qualification.
