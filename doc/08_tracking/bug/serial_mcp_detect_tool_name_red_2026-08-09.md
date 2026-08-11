# `detect_tool_name` fails to extract the tool name from a `tools/call` body

- **Status:** OPEN (RED, pre-existing)
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
