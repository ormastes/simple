# How to Use the Simple Language MCP Server

## ✅ Installation Status: COMPLETE

Your MCP server is fully installed and ready to use!

## Quick Start

### 1. Restart Claude Desktop

```bash
# Close and reopen the Claude Desktop application
# The MCP server will connect automatically
```

### 2. Verify Connection

In Claude Desktop, look for:
- MCP server indicator in the UI
- "simple-lang" in the connected servers list
- Tools become available when you type

### 3. Try These Commands

Ask Claude Desktop (NOT in CLI):

#### View a Bug
```
"Show me bug BUG-001 using the bugdb_get tool"
```

#### Edit a File
```
"Use simple_edit to add a comment to line 1 of src/app/cli/main.spl saying 'CLI entry point'"
```

#### Check Syntax
```
"Use simple_check to validate the syntax of src/app/mcp/bootstrap/main_optimized.spl"
```

#### View Code Changes
```
"Use simple_diff to show me what changed in the last commit"
```

#### Debug a Test
```
"Create a debug session for test/app/mcp/bugdb_spec.spl using debug_create_session"
```

## Available Tools (30+)

### 🐛 Bug Database
- `bugdb_get` - Fetch a specific bug by ID
- `bugdb_add` - Create a new bug entry
- `bugdb_update` - Modify an existing bug

### 📝 File Operations
- `simple_read` - Read Simple source files
- `simple_edit` - Edit files with syntax validation
- `simple_multi_edit` - Batch edit multiple files
- `simple_run` - Execute Simple commands

### 🔍 Diagnostics
- `simple_check` - Syntax and type checking
- `simple_symbols` - Extract symbols from code
- `simple_status` - Get project status summary

### 📚 Version Control (Jujutsu)
- `simple_diff` - Show code changes
- `simple_log` - View commit history
- `simple_squash` - Combine commits
- `simple_new` - Create new change

### 🐞 Debugging (Full Debug Session Support)
- `debug_create_session` - Start a debug session
- `debug_list_sessions` - List active sessions
- `debug_close_session` - Close a session
- `debug_set_breakpoint` - Set breakpoints
- `debug_remove_breakpoint` - Remove breakpoints
- `debug_continue` - Continue execution
- `debug_step` - Step through code
- `debug_get_variables` - Inspect variables
- `debug_stack_trace` - View call stack
- `debug_evaluate` - Evaluate expressions

### 📋 Debug Logging
- `debug_log_enable` - Enable logging for scopes
- `debug_log_disable` - Disable logging
- `debug_log_clear` - Clear log history
- `debug_log_query` - Search logs
- `debug_log_tree` - View log hierarchy
- `debug_log_status` - Check logging status

## Testing via Terminal

The MCP server uses **stdio protocol** (JSON-RPC over stdin/stdout). You can test in terminal if
you send correctly framed JSON-RPC messages (with `Content-Length` headers).

Recommended local regression path:

```bash
SIMPLE_LIB=src bin/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
```

This integration spec validates initialize, tools/resources listing, error handling, and
`debug_log_tree(format=json)` over real stdio transport.

## Configuration Details

**Location:** `~/.config/Claude/claude_desktop_config.json`

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

## Performance

- **Startup:** <1 second (optimized bootstrap)
- **Tool Discovery:** <10ms (pre-computed schemas)
- **First Tool Call:** 1-3 seconds (interpreter warmup)
- **Cached Calls:** <200ms

## Troubleshooting

### "simple-lang" Not Showing in Claude Desktop

1. **Check config exists:**
   ```bash
   cat ~/.config/Claude/claude_desktop_config.json
   ```

2. **Verify binary is executable:**
   ```bash
   ls -la /home/ormastes/dev/pub/simple/bin/simple_mcp_server_optimized
   ```

3. **Restart Claude Desktop** - Must restart to load config changes

### Tools Not Working

1. **Check project root:**
   ```bash
   echo $SIMPLE_PROJECT_ROOT
   # Should output: /home/ormastes/dev/pub/simple
   ```

2. **Verify database exists:**
   ```bash
   ls -la /home/ormastes/dev/pub/simple/doc/bug/bug_db.sdn
   ```

3. **Check Claude Desktop logs:**
   - Linux: `~/.config/Claude/logs/`
   - macOS: `~/Library/Logs/Claude/`

## Testing Scripts

Created for verification:

```bash
# Quick verification
./test_mcp_working.sh

# Smoke test
python3 test_mcp_smoke.py
```

These scripts verify:
- ✅ Binary exists and is executable
- ✅ Configuration is correct
- ✅ Server starts without crashing

## Next Steps

### To Use Now
1. **Restart Claude Desktop**
2. **Look for "simple-lang" server**
3. **Start asking Claude to use the tools!**

### Future Enhancements

Want to add more tools? Edit:
- **Tool schemas:** `src/mcp_lib/schema.spl`
- **Tool handlers:** `src/app/mcp/bootstrap/main_optimized.spl`
- **Rebuild:** `bin/simple build src/app/mcp/bootstrap/main_optimized.spl`

## Resources

- **Installation Guide:** `MCP_INSTALLATION_GUIDE.md`
- **Quick Start:** `MCP_QUICK_START.md`
- **Verification Report:** `MCP_VERIFICATION_COMPLETE.md`
- **Implementation Report:** `doc/report/cleanup_and_mcp_completion_2026-02-13.md`

---

**You're all set!** 🚀 Just restart Claude Desktop and start using your 30+ Simple Language MCP tools.
