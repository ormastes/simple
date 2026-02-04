# MCP Setup and Usage Guide

**Model Context Protocol (MCP) Integration for Simple Language**

## Overview

The Simple language project includes a fully functional MCP server that provides codebase access tools for AI assistants like Claude Code. The MCP server is written in Simple and integrates seamlessly with the project.

## Current Status

✅ **MCP is already installed and configured** in this project!

| Component | Status | Location |
|-----------|--------|----------|
| MCP Configuration | ✅ Complete | `.mcp.json` |
| MCP Server Implementation | ✅ Complete | `src/app/mcp/main.spl` |
| Runtime Binary | ✅ Available | `bin/simple_runtime` |
| Documentation | ✅ This guide | `doc/guide/mcp_setup_and_usage.md` |

## Configuration

### MCP Configuration File

**File**: `.mcp.json` (project root)

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "/home/ormastes/dev/pub/simple/bin/simple_runtime",
      "args": ["src/app/mcp/main.spl", "server"]
    }
  }
}
```

### What This Means

- **Server Name**: `simple-mcp`
- **Command**: Uses the Simple runtime binary
- **Script**: Runs the MCP server implementation (`src/app/mcp/main.spl`)
- **Mode**: Server mode (JSON-RPC over stdio)

## Available Tools

The MCP server provides 4 tools for codebase interaction:

### 1. `read` - Read File Contents

Reads and returns the complete contents of a file.

**Parameters**:
- `path` (string): Relative or absolute file path

**Example**:
```
Read src/compiler/backend.spl
```

**Use Cases**:
- Reading source code
- Examining configuration files
- Reviewing documentation

---

### 2. `search` - Search Code

Searches for patterns in the codebase using regex.

**Parameters**:
- `pattern` (string): Search pattern (supports regex)
- `path` (string, optional): Limit search to specific directory

**Example**:
```
Search for "fn eval_expr" in src/compiler/
```

**Use Cases**:
- Finding function definitions
- Locating specific code patterns
- Discovering API usage

---

### 3. `list_files` - List Directory Contents

Lists all files in a directory (recursive).

**Parameters**:
- `path` (string): Directory path to list

**Example**:
```
List all files in src/app/mcp/
```

**Use Cases**:
- Exploring directory structure
- Finding related files
- Understanding module organization

---

### 4. `file_info` - Get File Metadata

Returns metadata about a file (size, last modified, etc.).

**Parameters**:
- `path` (string): File path

**Example**:
```
Get info about src/compiler/backend.spl
```

**Use Cases**:
- Checking file size
- Verifying file existence
- Getting modification time

## Usage with Claude Code

### Setup

1. **Ensure Claude Code is installed**:
   ```bash
   # Claude Code CLI should be available
   claude --version
   ```

2. **Navigate to the Simple project**:
   ```bash
   cd /home/ormastes/dev/pub/simple
   ```

3. **Start Claude Code**:
   ```bash
   claude code
   ```

4. **Verify MCP server discovery**:
   - Claude Code automatically reads `.mcp.json`
   - The `simple-mcp` server should be available
   - Check with: "What MCP servers are available?"

### Example Interactions

#### Reading Code
```
User: Read the static method implementation in src/compiler/backend.spl
Claude: [Uses MCP read tool to fetch file contents]
```

#### Searching
```
User: Find all uses of MethodCall in the compiler
Claude: [Uses MCP search tool with pattern "MethodCall"]
```

#### Exploring
```
User: What files are in the MCP module?
Claude: [Uses MCP list_files for src/app/mcp/]
```

#### Investigation
```
User: How large is the backend.spl file?
Claude: [Uses MCP file_info tool]
```

## Implementation Details

### MCP Server (`src/app/mcp/main.spl`)

The MCP server is implemented in Simple language and handles:
- JSON-RPC message parsing
- Tool invocation
- File system operations
- Error handling
- Response formatting

**Key Features**:
- ✅ Stdio transport (standard JSON-RPC)
- ✅ 4 core tools implemented
- ✅ Error handling with proper MCP error codes
- ✅ Path resolution (relative and absolute)
- ✅ Integration with Simple's file I/O system

### Architecture

```
┌─────────────┐
│ Claude Code │
└──────┬──────┘
       │ JSON-RPC over stdio
       │
┌──────▼──────────────┐
│ simple_runtime      │ (Rust binary)
│   │                 │
│   └─> main.spl      │ (Simple MCP server)
│       └─> File I/O  │ (SFFI wrappers)
└─────────────────────┘
```

## Testing

### Manual Test

```bash
# Test MCP server startup
/home/ormastes/dev/pub/simple/bin/simple_runtime src/app/mcp/main.spl server

# Expected: Server starts and waits for JSON-RPC input
# (Press Ctrl+C to exit)
```

### Testing Tools

```bash
# Test read tool
echo '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"read","arguments":{"path":"README.md"}}}' | \
  /home/ormastes/dev/pub/simple/bin/simple_runtime src/app/mcp/main.spl server

# Expected: JSON response with file contents
```

## Troubleshooting

### MCP Server Not Starting

**Symptoms**: Server fails to start or immediately exits

**Solutions**:
1. Verify runtime binary exists:
   ```bash
   ls -la /home/ormastes/dev/pub/simple/bin/simple_runtime
   ```

2. Check MCP script exists:
   ```bash
   ls -la src/app/mcp/main.spl
   ```

3. Test runtime manually:
   ```bash
   /home/ormastes/dev/pub/simple/bin/simple_runtime src/app/mcp/main.spl --help
   ```

### Tools Not Working

**Symptoms**: Tools return errors or empty results

**Solutions**:
1. Check file paths are correct (relative to project root)
2. Verify permissions on files
3. Ensure pattern syntax is valid for search

### Claude Code Not Finding Server

**Symptoms**: MCP server not discovered by Claude Code

**Solutions**:
1. Verify `.mcp.json` exists in project root:
   ```bash
   cat .mcp.json
   ```

2. Check JSON syntax is valid:
   ```bash
   python3 -m json.tool .mcp.json
   ```

3. Restart Claude Code after configuration changes

## Extending the MCP Server

### Adding New Tools

To add a new tool to the MCP server:

1. **Define the tool in `src/app/mcp/main.spl`**:
   ```simple
   fn handle_my_tool(params: Dict) -> Result<text, text>:
       # Implementation here
       Ok("result")
   ```

2. **Register in tool list**:
   ```simple
   val tools = [
       Tool(name: "read", description: "..."),
       Tool(name: "search", description: "..."),
       Tool(name: "my_tool", description: "..."),  # Add here
   ]
   ```

3. **Add handler dispatch**:
   ```simple
   match tool_name:
       "read": handle_read(args)
       "search": handle_search(args)
       "my_tool": handle_my_tool(args)  # Add here
   ```

4. **Test the new tool**:
   ```bash
   # Test via JSON-RPC
   echo '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"my_tool","arguments":{}}}' | \
     ./bin/simple_runtime src/app/mcp/main.spl server
   ```

### Example: Adding a "count_lines" Tool

```simple
fn handle_count_lines(params: Dict) -> Result<text, text>:
    val path = params.get("path")?
    val content = file_read(path)
    val lines = content.split("\n").len()
    Ok("File has {lines} lines")
```

## Performance Considerations

### Startup Time

- **Cold start**: ~1-2 seconds (loading runtime + modules)
- **Tool execution**: <100ms for most operations
- **Large file reads**: Proportional to file size

### Optimization Tips

1. **Use specific paths**: Narrow search scope when possible
2. **Limit recursive operations**: Be specific with directory paths
3. **Cache results**: Claude Code may cache tool results

## Security

### Sandboxing

The MCP server operates with the same permissions as the Simple runtime:
- ✅ Read access to project files
- ✅ Write access (if needed for future tools)
- ⚠️  No network access by default
- ⚠️  Runs in user space (no elevated privileges)

### Best Practices

1. **Validate inputs**: All tool parameters are validated
2. **Path constraints**: Paths are resolved safely
3. **Error handling**: Failures are caught and reported properly
4. **No arbitrary code execution**: Tools are fixed, not dynamic

## Future Enhancements

Potential additions for the MCP server:

### Planned Tools

- `write`: Write file contents
- `grep_advanced`: More sophisticated search with filters
- `get_definition`: Find symbol definitions
- `get_references`: Find all references to a symbol
- `analyze_dependencies`: Show module dependencies

### Planned Features

- 🔄 Caching for frequently accessed files
- 🔄 Incremental search results
- 🔄 Syntax-aware operations
- 🔄 Integration with Simple's type system

## Related Documentation

- MCP Specification: https://modelcontextprotocol.io/docs
- Simple Language Guide: `doc/guide/syntax_quick_reference.md`
- SFFI Documentation: See `/sffi` skill
- File I/O: `src/app/io/mod.spl`

## Support

For issues or questions:

1. Check this guide
2. Review `src/app/mcp/main.spl` implementation
3. Test manually with JSON-RPC commands
4. Report issues to project maintainer

---

**Status**: MCP is fully functional and ready to use!

**Last Updated**: 2026-02-04
