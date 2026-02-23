# MCP Debug Output Fix - 2026-02-15

## Problem

When running `bin/simple mcp` or any MCP server, excessive debug output from the Rust runtime was polluting stderr:

```
[DEBUG] register_definitions: processing 157 items
[DEBUG] register_definitions: processing node type: Discriminant(56)
[DEBUG] register_definitions: processing node type: Discriminant(22)
...
```

This made the MCP server appear broken when it was actually functioning correctly. The debug output was coming from the compiled Rust runtime (`bin/release/simple`), specifically from the interpreter module's `register_definitions` function.

## Root Cause

The debug logging is compiled into the release binary at:
```
compiler/src/interpreter/interpreter_module/module_evaluator/evaluation_helpers.rs
```

Function signature (demangled from binary):
```
_ZN15simple_compiler11interpreter18interpreter_module16module_evaluator18evaluation_helpers20register_definitions17h311abd67a1479426E
```

The runtime was built with debug symbols and logging enabled.

## Solution

Created a wrapper script `bin/mcp_quiet.sh` that redirects stderr to `/dev/null`, suppressing the debug output while preserving stdout for MCP protocol JSON responses:

```bash
#!/bin/bash
# MCP Server Wrapper - Suppresses runtime debug output
exec "$@" 2>/dev/null
```

## Changes Made

1. **Created wrapper script** - `bin/mcp_quiet.sh`
   - Redirects stderr to `/dev/null`
   - Preserves stdout for MCP protocol
   - Made executable with `chmod +x`

2. **Updated `.mcp.json`** - All three MCP servers now use the wrapper:
   - `simple-mcp`: Full MCP server (33 tools)
   - `simple-mcp-jj`: JJ lite server (10 jj tools)
   - `simple-mcp-fileio`: File I/O server

Before:
```json
{
  "command": "/home/ormastes/dev/pub/simple/bin/release/simple",
  "args": ["/home/ormastes/dev/pub/simple/src/app/mcp/main.spl"]
}
```

After:
```json
{
  "command": "/home/ormastes/dev/pub/simple/bin/mcp_quiet.sh",
  "args": ["/home/ormastes/dev/pub/simple/bin/release/simple", "/home/ormastes/dev/pub/simple/src/app/mcp/main.spl"]
}
```

## Verification

All MCP servers now work correctly with clean output:

```bash
# Test simple-mcp
echo '{"jsonrpc":"2.0","id":1,"method":"initialize",...}' | \
  bin/mcp_quiet.sh bin/release/simple src/app/mcp/main.spl
# Output: Clean JSON response with 33 tools

# Test simple-mcp-jj
echo '{"jsonrpc":"2.0","id":1,"method":"initialize",...}' | \
  bin/mcp_quiet.sh bin/release/simple src/app/mcp_jj/main_lite.spl
# Output: Clean JSON response with 10 jj tools
```

## Alternative Solutions Considered

1. **Rebuild runtime without debug logging** - Would require modifying Rust source and rebuilding, slower to implement
2. **Add environment variable flag** - Runtime doesn't currently support this
3. **Modify Python proxy** - Already handles stderr separately, but wrapper is simpler for direct invocations

## Future Improvements

- Consider adding a build flag to disable debug output in release builds
- Add environment variable `SIMPLE_DEBUG=0` to runtime for controlling log levels
- Document this pattern for other CLI tools that may have similar issues

## Testing

Tested with:
- ✅ Direct invocation via wrapper script
- ✅ MCP Inspector (`npx @modelcontextprotocol/inspector`)
- ✅ Claude Desktop (via `.mcp.json`)
- ✅ All three MCP servers (simple-mcp, simple-mcp-jj, simple-mcp-fileio)

## Related Files

- `bin/mcp_quiet.sh` - Wrapper script (new)
- `.mcp.json` - MCP server configuration (updated)
- `memory/mcp_server.md` - MCP server documentation (to be updated)
