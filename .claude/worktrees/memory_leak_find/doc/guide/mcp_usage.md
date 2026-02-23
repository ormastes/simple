# Simple MCP Server - Usage Guide

## Installation in Claude Code

The Simple MCP server has been installed in Claude Code!

**Configuration:** `~/.config/claude/config.json`

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "/home/ormastes/dev/pub/simple/bin/simple_mcp_server",
      "args": [],
      "env": {}
    }
  }
}
```

## Available Tools (7 total)

### Code Reading Tools

1. **read_code** - Read a Simple language source file
   - Input: `path` (string) - File path
   - Annotations: read-only, idempotent
   - Example: "Read the file src/app/mcp/main.spl"

2. **list_files** - List Simple language files in a directory
   - Input: `path` (string, optional) - Directory path
   - Annotations: read-only, idempotent
   - Example: "List all .spl files in src/app/"

3. **search_code** - Search for code patterns
   - Input: `query` (string) - Search query
   - Annotations: read-only, idempotent
   - Example: "Search for 'extract_json_string' in the codebase"

4. **file_info** - Get file information (lines, functions, classes)
   - Input: `path` (string) - File path
   - Annotations: read-only, idempotent
   - Example: "Get info about src/app/mcp/main.spl"

### Bug Database Tools

5. **bugdb_get** - Get bug by ID
   - Input: `id` (string) - Bug ID
   - Annotations: read-only, idempotent
   - Example: "Get bug with ID bug_042"

6. **bugdb_add** - Add new bug to database
   - Input: `bug` (string) - Bug JSON data
   - Annotations: writable, non-idempotent
   - Example: "Add a new bug for the type inference issue"

7. **bugdb_update** - Update existing bug
   - Input: `id` (string) - Bug ID
   - Annotations: writable, idempotent
   - Example: "Update bug bug_042 status to resolved"

## Testing in Claude Code

### Method 1: Ask Claude Code to Use MCP Tools

Once Claude Code restarts with the new configuration, you can ask:

- "Use the simple-mcp server to read src/app/mcp/main.spl"
- "Search the Simple codebase for 'extract_json_string'"
- "List all files in src/app/mcp/"
- "Get bug information from the bug database"

### Method 2: Manual Testing (CLI)

Test the server directly from command line:

```bash
# Initialize
echo 'Content-Length: 161

{"jsonrpc":"2.0","id":"1","method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"test","version":"1.0"}}}' | bin/simple_mcp_server

# List tools
echo 'Content-Length: 52

{"jsonrpc":"2.0","id":"2","method":"tools/list"}' | bin/simple_mcp_server

# Call a tool
echo 'Content-Length: 103

{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"list_files","arguments":{"path":"src/app/mcp"}}}' | bin/simple_mcp_server
```

## Server Features

✅ **Protocol:** JSON-RPC 2.0 over stdio  
✅ **MCP Version:** 2025-06-18  
✅ **Capabilities:**
- Tools (7 tools with annotations)
- Resources (file system access)
- Prompts (refactoring, generation, analysis)
- Logging (setLevel support)

✅ **Tool Annotations:**
- `readOnlyHint` - Safe to call, won't modify state
- `destructiveHint` - May delete or overwrite data
- `idempotentHint` - Same result on repeated calls
- `openWorldHint` - Results may change over time

✅ **Server Instructions:**
"Search for Simple MCP tools when the user asks about Simple language source code, bugs, tests, or features. Provides code reading (read_code, list_files, search_code, file_info), bug tracking (bugdb_get, bugdb_add, bugdb_update), feature tracking, and test result tools."

## Restarting Claude Code

After updating the configuration, restart Claude Code to load the new MCP server:

```bash
# If using systemd
systemctl --user restart claude-code

# Or kill and restart manually
pkill -f claude
claude-code
```

## Troubleshooting

### Server Won't Start

1. Check if the wrapper script is executable:
   ```bash
   ls -la /home/ormastes/dev/pub/simple/bin/simple_mcp_server
   chmod +x /home/ormastes/dev/pub/simple/bin/simple_mcp_server
   ```

2. Test the server manually:
   ```bash
   echo 'Content-Length: 52

   {"jsonrpc":"2.0","id":"1","method":"initialize"}' | bin/simple_mcp_server
   ```

3. Check the runtime binary exists:
   ```bash
   ls -la /home/ormastes/dev/pub/simple/bin/release/simple_runtime
   ```

### Configuration Issues

Validate the JSON configuration:
```bash
cat ~/.config/claude/config.json | python3 -m json.tool
```

### View Server Logs

The wrapper script suppresses stderr by default. To see logs:

1. Edit `bin/simple_mcp_server` and remove `2>/dev/null`
2. Set `RUST_LOG=debug` for verbose logging

## Next Steps

- [ ] Restart Claude Code to load the MCP server
- [ ] Test with: "Use simple-mcp to list files in src/app/mcp/"
- [ ] Try bug database queries
- [ ] Explore prompt templates for refactoring

**Status:** ✅ Installed and ready to use!
