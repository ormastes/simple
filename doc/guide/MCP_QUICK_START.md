# Simple MCP Server - Quick Start

## ✓ Installation Complete!

The Simple Language MCP server is installed and configured for Claude Desktop.

## What Just Happened

1. ✓ MCP server binaries are built (`bin/simple_mcp_server_optimized`)
2. ✓ Claude Desktop config updated (`~/.config/Claude/claude_desktop_config.json`)
3. ✓ Bug database integration enabled (bugdb_get, bugdb_add, bugdb_update)
4. ✓ 30+ MCP tools available for code editing, debugging, and project management

## Next Step: Restart Claude Desktop

```bash
# Close and reopen Claude Desktop application
# The MCP server will automatically connect on startup
```

## Verify It's Working

After restarting Claude Desktop, ask:

> "Can you list the available Simple MCP tools?"

You should see tools like:
- `bugdb_get` - Query bugs
- `simple_edit` - Edit files
- `debug_create_session` - Debug code
- `simple_diff` - Show changes
- And many more...

## Try These Examples

### Example 1: Query the Bug Database
```
"Show me all critical bugs using the bug database"
```

### Example 2: Edit a File
```
"Use simple_edit to add a comment at the top of src/app/cli/main.spl"
```

### Example 3: Check Project Status
```
"What's the current status of the Simple compiler project?"
```

### Example 4: Create a Debug Session
```
"Debug the file test/app/mcp/bugdb_spec.spl and set a breakpoint at line 10"
```

## Full Documentation

See `MCP_INSTALLATION_GUIDE.md` for complete documentation.

## Configuration Details

**Server:** `/home/ormastes/dev/pub/simple/bin/simple_mcp_server_optimized`
**Config:** `~/.config/Claude/claude_desktop_config.json`
**Project:** `/home/ormastes/dev/pub/simple`

---

**That's it!** The MCP server is ready to use. 🚀
