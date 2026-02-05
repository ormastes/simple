# Simple MCP Server - Installation Status

## Configuration

**File:** `.mcp.json`
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

**Server:** `src/app/mcp/main.spl`
**Runtime:** Simple Language Interpreter

---

## Available Tools

### 1. `read_code`
Read and analyze Simple source files

**Parameters:**
- `path` (string) - Path to .spl file

**Example:**
```bash
simple mcp tool read_code --path="src/compiler/driver.spl"
```

### 2. `list_files`
List Simple files in a directory

**Parameters:**
- `path` (string) - Directory path (default: ".")

**Example:**
```bash
simple mcp tool list_files --path="src/compiler/"
```

### 3. `search_code`
Search for patterns in codebase

**Parameters:**
- `query` (string) - Search pattern

**Example:**
```bash
simple mcp tool search_code --query="hir_modules"
```

### 4. `file_info`
Get file statistics

**Parameters:**
- `path` (string) - Path to .spl file

**Returns:**
- Line count
- Function count
- Class/struct count

**Example:**
```bash
simple mcp tool file_info --path="src/compiler/driver.spl"
```

---

## Available Resources

### Static Resources

#### `project:///info`
Project metadata and configuration

**Returns:**
- Project name
- Version
- Structure
- Build configuration

### Dynamic Resource Templates

#### `file:///{path}`
Read file contents

**Example URIs:**
- `file:///src/compiler/driver.spl`
- `file:///README.md`
- `file:///doc/guide/syntax.md`

#### `symbol:///{name}`
Symbol information

**Example URIs:**
- `symbol:///Parser`
- `symbol:///compile_module`
- `symbol:///HIRModule`

**Returns:**
- Symbol location
- Type information
- Documentation
- References

#### `type:///{name}`
Type information

**Example URIs:**
- `type:///Parser`
- `type:///CompilerContext`
- `type:///Result`

**Returns:**
- Type definition
- Fields/methods
- Trait implementations
- Usage examples

#### `docs:///{path}`
Documentation resources

**Example URIs:**
- `docs:///getting_started`
- `docs:///api/compiler`
- `docs:///guide/testing`

#### `tree:///{path}`
Directory tree structure

**Example URIs:**
- `tree:///src/compiler`
- `tree:///test`
- `tree:///doc`

**Returns:**
- Directory structure
- File listing
- Statistics

### NEW: Bug Database Resources

#### `bugdb://all`
All bugs in database

#### `bugdb://open`
Open, investigating, and confirmed bugs

#### `bugdb://critical`
P0 and P1 severity bugs

#### `bugdb://important`
Important items (non-bugs)

#### `bugdb://stats`
Bug database statistics

**Returns:**
```json
{
  "total": 15,
  "open": 3,
  "fixed": 10,
  "p0": 0,
  "p1": 2,
  "important": 1,
  "health": "good"
}
```

#### `bugdb://bug/{id}`
Single bug by ID

**Example:**
- `bugdb://bug/parser_multiline_001`

---

## Available Prompts

### Refactoring Prompts

#### `refactor/rename`
Rename symbol across codebase

**Arguments:**
- `symbol` - Symbol to rename
- `new_name` - New name

#### `refactor/extract_function`
Extract code into new function

**Arguments:**
- `file` - File path
- `start_line` - Start line
- `end_line` - End line
- `function_name` - New function name

#### `refactor/inline`
Inline function call

**Arguments:**
- `file` - File path
- `function_name` - Function to inline

### Code Generation Prompts

#### `generate/tests`
Generate test cases for code

**Arguments:**
- `file` - File path
- `function_name` - Function to test

#### `generate/trait_impl`
Generate trait implementation

**Arguments:**
- `type` - Type name
- `trait` - Trait name

#### `generate/constructor`
Generate constructor for type

**Arguments:**
- `type` - Type name
- `style` - Constructor style (default/builder/etc)

### Documentation Prompts

#### `docs/add_docstrings`
Add documentation to code

**Arguments:**
- `file` - File path
- `symbol` - Optional symbol name

#### `docs/explain_code`
Explain code section

**Arguments:**
- `file` - File path
- `start_line` - Start line
- `end_line` - End line

#### `docs/generate_readme`
Generate README documentation

**Arguments:**
- `directory` - Directory path

#### `docs/api_reference`
Generate API reference

**Arguments:**
- `module` - Module name

### Debugging Prompts

#### `debug/analyze_error`
Analyze error message

**Arguments:**
- `error` - Error message
- `file` - Optional file path

#### `debug/trace_execution`
Trace execution path

**Arguments:**
- `function` - Function name
- `file` - File path

---

## Usage

### Start MCP Server

```bash
# From project root
./bin/simple_runtime src/app/mcp/main.spl server

# With debug logging
./bin/simple_runtime src/app/mcp/main.spl server --debug
```

### CLI Mode

```bash
# Read file
simple mcp read file:///src/compiler/driver.spl

# Search
simple mcp search "hir_modules"

# File info
simple mcp info src/compiler/driver.spl

# Bug stats
simple mcp read bugdb://stats
```

### MCP Protocol

The server implements the full MCP protocol:
- `initialize` - Initialize connection
- `tools/list` - List available tools
- `tools/call` - Call a tool
- `resources/list` - List available resources
- `resources/read` - Read a resource
- `resources/templates/list` - List resource templates
- `prompts/list` - List available prompts
- `prompts/get` - Get a prompt

---

## Integration with Claude Code

The MCP server integrates with Claude Code (CLI):

1. **Automatic Discovery:** Claude Code reads `.mcp.json`
2. **Tool Invocation:** Claude can call MCP tools directly
3. **Resource Access:** Claude can read MCP resources
4. **Prompt Templates:** Claude can use prompts for common tasks

---

## File Structure

```
.mcp.json                      # MCP configuration
src/app/mcp/
├── main.spl                   # MCP server implementation
├── resources.spl              # Resource providers
├── prompts.spl                # Prompt templates
├── editor.spl                 # Editor integration
├── session.spl                # Session management
└── bugdb_resource.spl         # Bug database integration (NEW)

src/app/bugdb/                 # Bug database (NEW)
├── mod.spl
├── atomic_db.spl
└── manager.spl
```

---

## Status

✅ **MCP Server:** Installed and configured
✅ **Tools:** 4 tools available
✅ **Resources:** 7 resource types
✅ **Prompts:** 12 prompts available
✅ **Bug Database:** Integrated with MCP
✅ **Documentation:** Complete

**Ready to use!** 🚀

---

## Next Steps

### To Test MCP Server

```bash
# 1. Start server
./bin/simple_runtime src/app/mcp/main.spl server --debug

# 2. In another terminal, test with curl
echo '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | \
  ./bin/simple_runtime src/app/mcp/main.spl server

# 3. Or use Claude Code integration (automatic)
```

### To Add Bug to Database

```bash
# Run the example script
./bin/simple_runtime scripts/add_multiline_issue.spl

# Or in your code
from app.bugdb.manager import add_bug, BugSeverity

add_bug(
    id: "my_bug_001",
    severity: BugSeverity.P1,
    title: "Bug description",
    description: ["Details..."],
    file: "src/file.spl",
    line: 42
)
```

### To Query Bug Database via MCP

```bash
# Get all bugs
simple mcp read bugdb://all

# Get critical bugs
simple mcp read bugdb://critical

# Get stats
simple mcp read bugdb://stats

# Query bugs
simple mcp query bugs --query="parser"
```
