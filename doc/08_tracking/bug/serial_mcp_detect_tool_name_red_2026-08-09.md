# `detect_tool_name` fails to extract the tool name from a `tools/call` body

- **Status:** RESOLVED (2026-09-12) — the helper was deleted by the McpServer migration; the two examples now exercise the facade dispatch that replaced it (13/13)
- **Found:** 2026-08-09, while auditing `serial_mcp_spec.spl` for tautology shells
- **Severity:** medium — MCP tool dispatch cannot identify which tool was invoked

## Symptom

Two examples in `test/01_unit/app/serial_mcp/serial_mcp_spec.spl` are RED:

```
✗ AC-5: extracts tool name from tools/call body
✗ AC-5: extracts serial_open from body
```

Both call `detect_tool_name` (`src/app/serial_mcp/tools.spl`) with a
well-formed body and expect the `params.name` value back:

```simple
val body = "{\"params\":{\"name\":\"ssh_serial_exec\",\"arguments\":{}}}"
expect(detect_tool_name(body)).to_equal("ssh_serial_exec")
```

## Provenance — this is NOT caused by the 2026-08-09 spec edit

The tautology-shell audit that day changed only (a) the file's header comment
and (b) the `get_arg` example, which had been the vacuous
`expect(found or not found).to_equal(true)`. Neither failing example was
touched:

```
git diff -- test/01_unit/app/serial_mcp/serial_mcp_spec.spl \
  | grep -iE "detect_tool_name|tools/call"      # no hits
```

The two failures are therefore pre-existing. They are deliberately left RED
rather than weakened or marked pending — a correctly-failing spec documents a
real defect.

## Unblock condition

Fix `detect_tool_name` so it returns `params.name`, then:

```
SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test test/01_unit/app/serial_mcp/serial_mcp_spec.spl
```

must report 0 failures. Note the file exists twice — also update the identical
copy at `test/unit/app/serial_mcp/serial_mcp_spec.spl`.

## Related

- `doc/08_tracking/test/tautology_shell_spec_dispositions_2026-08-09.md` — why
  this file's four `BLOCKED:` hardware examples are kept as-is.

## Fix 2026-09-12 (BUGFIX-5)

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(Rust bootstrap seed, sha256 `3d120a6f`), worktree `/home/yoon/dev/simple-bugfix-5`
at base `89c5e3f865d`.

RED, as recorded:

```
SPEC FILE VERDICT: test/01_unit/app/serial_mcp/serial_mcp_spec.spl outcome=ERROR declared>=13 executed=13 passed=11 failed=2
  ✗ AC-5: extracts tool name from tools/call body
    semantic: function `detect_tool_name` not found
  ✗ AC-5: extracts serial_open from body
    semantic: function `detect_tool_name` not found
```

**The record's unblock condition ("fix `detect_tool_name` so it returns
`params.name`") was not actionable as written: the function does not exist.**
`src/app/serial_mcp/tools.spl` defines `get_arg`, `get_arg_int` and the five
`handle_*` entry points and nothing else; the only `detect_tool_name` in the
tree is `src/app/simple_lsp_mcp/tools.spl:336`, which is an LSP-tool allowlist
and returns `""` for `ssh_serial_exec`. The spec's `use
app.serial_mcp.tools.{detect_tool_name, ...}` resolved to nothing.

History explains it: serial-mcp was "Migrated to McpServer facade (Wave C3)"
(header of both `main.spl` and `tools.spl`), and that migration moved tool-name
dispatch into the SDK — `mcp_server_handle`
(`src/lib/nogc_sync_mut/mcp_sdk/server/app.spl:199-208`) reads `params` then
`params.name` and calls `registry_call(tool_name, args_raw)`. The app-local
helper was deleted; the spec kept importing it.

Re-adding a `detect_tool_name` to satisfy the import would have added product
code with no product caller (`.claude/rules/code-style.md`: never add unused
code). Instead the two examples now assert the **real** replacement path: they
register two probe tools through the facade and check that a `tools/call` body
naming one of them reaches that one and not the other.

```
GREEN test/01_unit/app/serial_mcp/serial_mcp_spec.spl outcome=OK declared>=13 executed=13 passed=13 failed=0
GREEN test/unit/app/serial_mcp/serial_mcp_spec.spl    outcome=OK declared>=13 executed=13 passed=13 failed=0
```

Discrimination (not a tautology): pointing the first example's expectation at
the other probe tool in a scratch copy fails exactly that example —
`outcome=ERROR declared>=13 executed=13 passed=12 failed=1`. The second example
additionally asserts the *other* tool's marker is absent, so a handler that ran
both would fail.

The four `BLOCKED:` hardware-gated examples were left exactly as the 2026-08-09
disposition note demands.

- Status: RESOLVED (2026-09-12) — 1485de62b91, spec test/01_unit/app/serial_mcp/serial_mcp_spec.spl (+ test/unit mirror)
