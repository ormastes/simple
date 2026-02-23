# Simple Language MCP Server - Installation Guide

## Status: ✓ Installed and Configured

The Simple Language MCP (Model Context Protocol) server is already built and configured for use with Claude Desktop.

## What's Installed

### 1. MCP Server Binaries

Located in `bin/`:
- `simple_mcp_server_optimized` - Main MCP server (recommended, <1s startup)
- `simple_mcp_server` - Standard MCP server
- `simple_mcp_server_legacy` - Legacy version
- `simple_mcp_fileio` - File I/O specific server

### 2. Server Implementation

Source code in `src/app/mcp/`:
- `bootstrap/main_optimized.spl` - Optimized single-process server
- `bugdb_resource.spl` - Bug database MCP resources
- `featuredb_resource.spl` - Feature database resources
- `testdb_resource.spl` - Test database resources
- `debug_*.spl` - Debugging tools
- `diag_*.spl` - Diagnostic and VCS tools
- And many more...

### 3. Claude Desktop Configuration

**Location:** `~/.config/Claude/claude_desktop_config.json`

**Current Configuration:**
```json
{
  "mcpServers": {
    "simple-lang": {
      "command": "/home/ormastes/dev/pub/simple/bin/simple_mcp_server_optimized",
      "args": ["server"],
      "env": {
        "SIMPLE_PROJECT_ROOT": "/home/ormastes/dev/pub/simple"
      }
    }
  }
}
```

## Available MCP Tools

The MCP server provides access to the following tool categories:

### Bug Database Tools
- `bugdb_get` - Query single bug by ID
- `bugdb_add` - Create new bug entry
- `bugdb_update` - Modify existing bug

### Diagnostic Tools
- `simple_edit` - Edit Simple language files
- `simple_multi_edit` - Edit multiple files at once
- `simple_run` - Run Simple commands
- `simple_read` - Read source files
- `simple_check` - Check syntax
- `simple_symbols` - Extract symbols
- `simple_status` - Get project status

### Version Control Tools (Jujutsu)
- `simple_diff` - Show diffs
- `simple_log` - Show commit history
- `simple_squash` - Squash commits
- `simple_new` - Create new change

### Debug Tools
- `debug_create_session` - Create debug session
- `debug_list_sessions` - List active sessions
- `debug_close_session` - Close debug session
- `debug_set_breakpoint` - Set breakpoints
- `debug_remove_breakpoint` - Remove breakpoints
- `debug_continue` - Continue execution
- `debug_step` - Step through code
- `debug_get_variables` - Get variable values
- `debug_stack_trace` - Get stack trace
- `debug_evaluate` - Evaluate expressions

### Debug Logging Tools
- `debug_log_enable` - Enable logging
- `debug_log_disable` - Disable logging
- `debug_log_clear` - Clear logs
- `debug_log_query` - Query logs
- `debug_log_tree` - Show log tree
- `debug_log_status` - Get logging status

## Available MCP Resources

The server provides read access to project databases:

- **Bug Database** (`doc/bug/bug_db.sdn`) - All project bugs
- **Feature Database** - Feature tracking
- **Test Database** - Test results and coverage

## How to Use

### 1. Restart Claude Desktop

After configuration changes, restart Claude Desktop to activate the MCP server.

### 2. Verify Connection

In Claude Desktop:
1. Look for an MCP indicator (usually in the UI)
2. Check if "simple-lang" server is connected
3. You should see the available tools in the context menu

### 3. Use MCP Tools

In your conversation with Claude, you can now:

```
# Query a specific bug
Can you show me bug BUG-001 using bugdb_get?

# Edit a file
Use simple_edit to fix the syntax error in src/app/cli/main.spl

# Check project status
What's the current status of the Simple project?

# Debug a test
Create a debug session for test/app/mcp/bugdb_spec.spl
```

### 4. Example Workflow

```
User: Can you check the bug database for all P0 bugs?
Claude: [Uses bugdb_query tool with filter="priority:P0"]

User: Show me the code for handling that bug
Claude: [Uses simple_read to read the relevant source file]

User: Can you fix that issue?
Claude: [Uses simple_edit to make changes]

User: Commit these changes
Claude: [Uses simple_new to create a commit]
```

## Troubleshooting

### Server Won't Start

Check the logs in Claude Desktop:
- macOS: `~/Library/Logs/Claude/`
- Linux: `~/.config/Claude/logs/`

### Tools Not Showing Up

1. Verify the binary exists: `ls -la /home/ormastes/dev/pub/simple/bin/simple_mcp_server_optimized`
2. Check it's executable: `chmod +x /home/ormastes/dev/pub/simple/bin/simple_mcp_server_optimized`
3. Verify configuration file syntax: `cat ~/.config/Claude/claude_desktop_config.json | python3 -m json.tool`

### Permissions Issues

Ensure the MCP server has access to:
- Read project files
- Write to `doc/bug/bug_db.sdn`
- Execute `bin/simple` and other tools

## Performance Characteristics

The optimized MCP server is designed for low latency:

- **Initialize:** <800ms
- **Tools/list:** <10ms (pre-computed schemas)
- **First tool call:** <200ms (lazy load handler)
- **Cached tool call:** <50ms

## Recent Updates (2026-02-13)

✅ Integrated bug database with MCP server
✅ Added `bugdb_get`, `bugdb_add`, `bugdb_update` tools
✅ Updated configuration to use optimized server
✅ Cleaned up references to deleted interpreter module

## Next Steps

To extend the MCP server:

1. **Add new tools:** Edit `src/app/mcp/bootstrap/main_optimized.spl`
2. **Add new resources:** Create new `*_resource.spl` files
3. **Update schemas:** Edit `src/app/mcp/mcp_lib/schema.spl`
4. **Rebuild:** Run `bin/simple build src/app/mcp/bootstrap/main_optimized.spl`

## Documentation

For more details, see:
- `doc/report/cleanup_and_mcp_completion_2026-02-13.md` - Recent integration report
- `doc/plan/cleanup_and_mcp_plan_2026-02-13.md` - Original implementation plan
- `src/app/mcp/README.md` - MCP implementation details (if exists)

## Support

For issues or questions:
- Check project documentation in `doc/`
- Review `MEMORY.md` for known limitations
- See `CLAUDE.md` for development guidelines
