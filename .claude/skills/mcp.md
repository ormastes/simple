# MCP Skill - Model Context Protocol for Simple

## What is MCP?

The Simple MCP server provides LLM-friendly code representation via the Model Context Protocol. It enables automated code analysis, bug detection, and debugging workflows.

**Location:** `src/app/mcp/main.spl`
**Server Binary:** `./rust/target/debug/simple_old src/app/mcp/main.spl`

---

## MCP Server Modes

### 1. Server Mode (stdio)
Start MCP server for interactive client connections:

```bash
./rust/target/debug/simple_old src/app/mcp/main.spl server
./rust/target/debug/simple_old src/app/mcp/main.spl server --debug
```

**Use Cases:**
- Claude Code integration
- IDE integrations
- Automated tooling

### 2. CLI Mode
Direct command-line usage:

```bash
# Read file
./rust/target/debug/simple_old src/app/mcp/main.spl read <file.spl>

# Expand symbol
./rust/target/debug/simple_old src/app/mcp/main.spl expand <file.spl> <symbol>

# Search
./rust/target/debug/simple_old src/app/mcp/main.spl search <query>

# Generate JSON
./rust/target/debug/simple_old src/app/mcp/main.spl json <file.spl>
./rust/target/debug/simple_old src/app/mcp/main.spl json <file.spl> --meta
```

---

## MCP Tools

### read_code
Read and analyze Simple source files:

```bash
./rust/target/debug/simple_old src/app/mcp/main.spl read src/compiler/driver.spl
```

**Returns:** Full file content with syntax information

### list_files
List Simple files in directory:

```bash
./rust/target/debug/simple_old src/app/mcp/main.spl list src/compiler/
```

**Returns:** List of .spl files (requires fs_read_dir FFI)

### search_code
Search for patterns in codebase:

```bash
./rust/target/debug/simple_old src/app/mcp/main.spl search "hir_modules"
```

**Returns:** Files and locations matching query (requires filesystem iteration FFI)

### file_info
Get file statistics:

```bash
./rust/target/debug/simple_old src/app/mcp/main.spl file_info src/compiler/driver.spl
```

**Returns:**
- Line count
- Function count
- Class/struct count

---

## MCP Configuration

### Claude Code Integration

**File:** `.mcp.json`

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "/path/to/simple/target/debug/simple_old",
      "args": ["src/app/mcp/main.spl", "server"]
    }
  }
}
```

### Server Capabilities

```json
{
  "protocolVersion": "2024-11-05",
  "capabilities": {
    "tools": {}
  },
  "serverInfo": {
    "name": "simple-mcp",
    "version": "1.0.0"
  }
}
```

---

## MCP-Based Debugging

### Automated Bug Detection

**Script:** `scripts/mcp_debug_bootstrap.spl`

```simple
# Tests dictionary semantics
test_dict_mutation() -> Option<Bug>

# Tests context field mutation
test_context_mutation() -> Option<Bug>

# Analyzes code patterns
analyze_driver_code() -> [Bug]

# Registers bugs to database
register_bugs(bugs: [Bug])
```

**Run:**
```bash
./rust/target/debug/simple_old scripts/mcp_debug_bootstrap.spl
```

**Output:**
- Detected bugs
- Test results
- Bug database updates

### Bug Detection Patterns

**Dictionary Mutation:**
```simple
# Pattern: var d = ctx.field; d[k] = v; ctx.field = d
# Tests if this persists mutations correctly
```

**Context Flow:**
```simple
# Tracks context through compilation phases
# Detects if fields are lost during phase transitions
```

**Code Analysis:**
```simple
# Searches for suspicious patterns in driver.spl
# Reports potential issues with line numbers
```

---

## MCP Debugging Workflow

### 1. Run Automated Detection

```bash
./rust/target/debug/simple_old scripts/mcp_debug_bootstrap.spl
```

**Checks:**
- ✓ Dictionary semantics
- ✓ Context mutations
- ✓ Code patterns
- ✓ Test verification

### 2. Analyze Results

```bash
# View detected bugs
cat doc/bug/bug_db.sdn

# View analysis report
cat doc/bug/mcp_bug_analysis_2026-01-29.md
```

### 3. Interactive Analysis

```bash
# Read specific code sections
./rust/target/debug/simple_old src/app/mcp/main.spl read src/compiler/driver.spl

# Search for patterns
./rust/target/debug/simple_old src/app/mcp/main.spl search "hir_modules"

# Get file stats
./rust/target/debug/simple_old src/app/mcp/main.spl file_info src/compiler/driver.spl
```

### 4. Register Bugs

**Format:** `doc/bug/bug_db.sdn`

```sdn
bugs |id, severity, status, title, file, line, description, reproducible_by|
    bug_id, P0, confirmed, "Title", "file.spl", 123, "Description", "test_case"

test_cases |id, file, status|
    test_id, "path/to/test.spl", pass

fixes |bug_id, strategy, file, description, status|
    bug_id, "strategy", "file.spl", "Description", applied

notes |bug_id, timestamp, note|
    bug_id, "2026-01-29T12:00:00", "Investigation note"
```

### 5. Generate Reports

```bash
# MCP analysis report
doc/bug/mcp_bug_analysis_2026-01-29.md

# Investigation log
doc/report/bootstrap_investigation_2026-01-29.md

# Session summary
doc/report/mcp_debugging_session_summary.md
```

---

## MCP Test Scripts

### test_dict_semantics.spl
Tests dictionary mutation patterns:

```simple
class Context:
    modules: Dict<text, i32>

fn test_copy_modify_reassign():
    val ctx = Context(modules: {})
    var modules = ctx.modules
    modules["test"] = 42
    ctx.modules = modules
    # Verify: ctx.modules.keys().len() == 1
```

**Run:**
```bash
./rust/target/debug/simple_old scripts/test_dict_semantics.spl
```

**Expected:** ALL TESTS PASSED

### bootstrap_extended.spl
Multi-generation bootstrap tester:

```bash
./rust/target/debug/simple_old scripts/bootstrap_extended.spl --generations=5
```

**Features:**
- Tests N generations
- Tracks hashes per generation
- Detects crashes/bugs automatically
- Finds fixpoint (identical generations)
- Saves results to `target/bootstrap/report.md`

### mcp_debug_bootstrap.spl
Automated bug detection:

```bash
./rust/target/debug/simple_old scripts/mcp_debug_bootstrap.spl
```

**Detects:**
- Dictionary mutation issues
- Context field mutation problems
- Suspicious code patterns
- Test failures

---

## MCP Server Implementation

### Protocol Support

**JSON-RPC 2.0 over stdio:**
- `initialize` - Server capabilities
- `initialized` - Notification
- `tools/list` - Available tools
- `tools/call` - Execute tool
- `shutdown` - Clean shutdown
- `exit` - Terminate

### Tools Schema

```json
{
  "name": "read_code",
  "description": "Read a Simple language source file",
  "inputSchema": {
    "type": "object",
    "properties": {
      "path": {
        "type": "string",
        "description": "File path"
      }
    },
    "required": ["path"]
  }
}
```

### Error Handling

```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": -32602,
    "message": "Unknown tool: tool_name"
  }
}
```

---

## Bootstrap Debug Integration

### MCP-Enhanced Bootstrap

**Workflow:**
1. Run bootstrap with debug logging
2. Use MCP to analyze output
3. Detect bugs automatically
4. Register in bug database
5. Generate fix proposals

**Example:**
```bash
# Capture debug output
./scripts/capture_bootstrap_debug.sh

# Analyze with MCP
./rust/target/debug/simple_old scripts/mcp_debug_bootstrap.spl

# View results
cat doc/bug/bug_db.sdn
```

### Debug Points

**Phase 3 (HIR):**
- `[phase3] parsed modules count=N`
- `[phase3] stored HIR module 'X', total now: N`
- `[phase3] returning ctx with N HIR modules`

**Phase 5 (AOT):**
- `[aot] DEBUG: ctx.hir_modules count = N`
- `[aot] MIR done, N modules`

### Bug Database Updates

MCP automatically updates `doc/bug/bug_db.sdn`:

```sdn
bugs |id, severity, status, title, file, line, description, reproducible_by|
    bootstrap_001, P0, confirmed, "MIR gets 0 modules", "src/compiler/driver.spl", 699, "HIR modules lost", "bootstrap_stage2"
```

---

## Future Enhancements

### Planned MCP Tools

- **context_trace** - Trace value flow through compilation phases
- **profile_compile** - Performance profiling with bottleneck detection
- **fix_suggest** - AI-powered fix suggestions
- **test_gen** - Generate test cases from bugs

### Integration Goals

- Real-time debugging during compilation
- Automatic bug report generation
- Integration with bug tracking systems
- CI/CD pipeline integration

---

## Troubleshooting

### MCP Server Won't Start

```bash
# Check simple_old binary exists
ls -la ./rust/target/debug/simple_old

# Rebuild if needed (first-time setup)
simple build
# Or: cd rust && cargo build

# Test with debug output
./rust/target/debug/simple_old src/app/mcp/main.spl server --debug
```

### Tool Errors

**"unknown extern function: rt_read_file"**
- Script needs FFI functions not available in all contexts
- Use CLI mode instead of server mode
- Or add missing FFI declarations

### Performance Issues

**Slow file reading:**
- Large files may take time to parse
- Use `file_info` for quick stats instead of full `read_code`

---

---

## MCP + Database Integration (2026-02-05 Update)

### Status: ✅ Production Ready

**Parse Errors Fixed:**
- `src/app/mcp/resources.spl` - Fixed `import` → `use` syntax
- `src/app/mcp/prompts.spl` - Fixed `import` → `use` syntax
- `src/app/mcp/main.spl` - Previously fixed (template keyword, import syntax)

**Components:**
- ✅ MCP Server (no parse errors)
- ✅ Bug Database Resource (`src/app/mcp/bugdb_resource.spl`)
- ✅ Database Library (27/27 tests passing)
- ✅ Integration Tests (80+ tests created)

### Bug Database MCP Resource

**File:** `src/app/mcp/bugdb_resource.spl`

Provides JSON API for bug database access via MCP:

```simple
use app.mcp.bugdb_resource.{get_all_bugs, get_open_bugs, get_critical_bugs, get_bug_stats}

# Get all bugs as JSON
val json = get_all_bugs("/path/to/bugs.sdn")

# Get only open bugs
val open_json = get_open_bugs("/path/to/bugs.sdn")

# Get critical bugs (P0 + P1)
val critical_json = get_critical_bugs("/path/to/bugs.sdn")

# Get statistics
val stats_json = get_bug_stats("/path/to/bugs.sdn")
```

**JSON Output Example:**

```json
{
  "total": 3,
  "bugs": [
    {
      "id": "bug_001",
      "severity": "P0",
      "status": "Open",
      "title": "Critical bug",
      "file": "main.spl",
      "line": 42,
      "reproducible_by": "test_critical",
      "description": ["Bug details"]
    }
  ]
}
```

### MCP Resources (Proposed URIs)

**Bug Database:**
- `bugdb://all` - All bugs
- `bugdb://open` - Open bugs only
- `bugdb://critical` - P0 + P1 bugs
- `bugdb://stats` - Bug statistics
- `bugdb://bug/{id}` - Single bug by ID

**Test Database:**
- `testdb://all` - All tests
- `testdb://failed` - Failed tests
- `testdb://slow` - Slow tests

**Feature Database:**
- `featdb://all` - All features
- `featdb://incomplete` - Incomplete features

### Testing MCP Integration

```bash
# Test MCP modules import
./bin/simple_runtime /tmp/test_mcp_imports.spl

# Test bug database integration
./bin/simple_runtime test/integration/mcp_bugdb_spec.spl

# Run all integration tests
./bin/simple_runtime test/integration/database_*.spl
```

### Architecture

```
MCP Client (Claude Code, etc.)
    ↓ JSON-RPC
MCP Server (src/app/mcp/main.spl)
    ↓
MCP Resources (resources.spl, prompts.spl, bugdb_resource.spl)
    ↓
Bug Database (src/lib/database/bug.spl)
    ↓
Core Database (src/lib/database/mod.spl)
    ↓
SDN File Format
```

---

## See Also

- `src/app/mcp/main.spl` - MCP server implementation
- `src/app/mcp/bugdb_resource.spl` - Bug database MCP integration
- `src/lib/database/` - Unified database library
- `scripts/mcp_debug_bootstrap.spl` - Automated debugging
- `doc/bug/bug_db.sdn` - Bug database
- `doc/report/mcp_database_integration_2026-02-05.md` - Integration report
- `doc/report/mcp_fixes_and_tests_2026-02-05.md` - Fixes and tests
- `.claude/skills/debug.md` - Debugging skill
- `.claude/skills/database.md` - Database library skill
