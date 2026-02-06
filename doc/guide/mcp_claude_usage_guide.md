# MCP Features: Claude Usage Guide & Simple MCP Server Reference

**Date:** 2026-02-05
**Purpose:** Feature-by-feature guide showing how Claude uses each MCP feature, configuration examples, and Simple MCP server implementation status.

---

## Table of Contents

1. [Configuration](#1-configuration)
2. [Tools](#2-tools)
3. [Resources](#3-resources)
4. [Prompts](#4-prompts)
5. [Progress Notifications](#5-progress-notifications)
6. [Logging](#6-logging)
7. [Sampling](#7-sampling)
8. [Elicitation](#8-elicitation)
9. [Roots](#9-roots)
10. [Tasks](#10-tasks)
11. [Notifications (list_changed)](#11-notifications-list_changed)
12. [Resource Subscriptions](#12-resource-subscriptions)
13. [Tool Annotations](#13-tool-annotations)
14. [Structured Output](#14-structured-output)
15. [Pagination](#15-pagination)
16. [Content Types](#16-content-types)
17. [Completions](#17-completions)
18. [Transport](#18-transport)
19. [Protocol Version](#19-protocol-version)
20. [Feature Support Matrix](#20-feature-support-matrix)
21. [Claude Code Built-in Tools](#21-claude-code-built-in-tools)
22. [Claude Code as MCP Server](#22-claude-code-as-mcp-server)
23. [Tool Search (MCPSearch) Internals](#23-tool-search-mcpsearch-internals)
24. [Permission Prompt Tool](#24-permission-prompt-tool)
25. [MCP Resource Access Tools](#25-mcp-resource-access-tools)
26. [Built-in Slash Commands](#26-built-in-slash-commands)
27. [Managed MCP Configuration](#27-managed-mcp-configuration)

---

## 1. Configuration

### Claude Code Configuration

**Three configuration scopes** (precedence: Local > Project > User):

| Scope | File | Shared | Use Case |
|-------|------|--------|----------|
| Local | `~/.claude.json` (per-project) | No | Personal MCP servers |
| Project | `.mcp.json` (project root) | Yes (git) | Team-shared servers |
| User | `~/.claude.json` (global) | No | Cross-project servers |

**CLI commands:**

```bash
# Add Simple MCP server (stdio)
claude mcp add --transport stdio simple-mcp -- simple mcp server

# Add with environment variables
claude mcp add --transport stdio --env PROJECT_ROOT=/path/to/project simple-mcp -- simple mcp server

# Add remote server (HTTP)
claude mcp add --transport http my-remote-server https://mcp.example.com/mcp

# List / remove
claude mcp list
claude mcp remove simple-mcp

# Import from Claude Desktop
claude mcp add-from-claude-desktop

# Load from config file
claude --mcp-config ./mcp.json
claude --strict-mcp-config --mcp-config ./mcp.json  # Only use this config
```

**`~/.claude.json` format:**

```json
{
  "mcpServers": {
    "simple-mcp": {
      "type": "stdio",
      "command": "simple",
      "args": ["mcp", "server"],
      "env": {}
    }
  }
}
```

**`.mcp.json` format (project-scoped, shareable):**

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "simple",
      "args": ["mcp", "server"],
      "env": {
        "PROJECT_ROOT": "${PWD}"
      }
    }
  }
}
```

Supports `${VAR}` and `${VAR:-default}` expansion in `command`, `args`, `env`, `url`, `headers`.

### Claude Desktop Configuration

**File:** `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS)

```json
{
  "mcpServers": {
    "simple-mcp": {
      "command": "simple",
      "args": ["mcp", "server"]
    }
  }
}
```

**Note:** Claude Desktop requires full restart after config changes. Remote servers use the Connectors UI, not the config file.

### Simple MCP Server Status

**Current:** `simple mcp server [--debug]` starts stdio server.
**Improvement:** Add `--port` flag for HTTP transport.

---

## 2. Tools

### How Claude Uses Tools

When Claude determines a task needs an MCP tool, it generates a `tools/call` request:

```
User: "What bugs are open in the project?"

Claude (internally):
1. Discovers `bugdb_get` tool via `tools/list`
2. Generates tool_use: bugdb_get with params
3. Claude Code sends JSON-RPC to MCP server
4. Server returns result
5. Claude formats response for user
```

**JSON-RPC flow:**

```json
// 1. Claude Code calls tools/list
{"jsonrpc":"2.0","id":1,"method":"tools/list"}

// 2. Server responds with tool definitions
{"jsonrpc":"2.0","id":1,"result":{"tools":[
  {"name":"read_code","description":"Read a Simple source file",
   "inputSchema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]}},
  {"name":"bugdb_get","description":"Get bug by ID",
   "inputSchema":{"type":"object","properties":{"id":{"type":"string"}},"required":["id"]}}
]}}

// 3. Claude Code calls the tool
{"jsonrpc":"2.0","id":2,"method":"tools/call",
 "params":{"name":"bugdb_get","arguments":{"id":"bug_042"}}}

// 4. Server returns result
{"jsonrpc":"2.0","id":2,"result":{
  "content":[{"type":"text","text":"{\"id\":\"bug_042\",\"title\":\"Parser crash\",\"status\":\"open\"}"}]
}}
```

### Permission Flow

Claude Code asks user approval before calling MCP tools:

```
Claude wants to use: bugdb_get (simple-mcp)
  Arguments: {"id": "bug_042"}

  [Allow once] [Always allow] [Deny]
```

Pre-configure in settings:
```json
{
  "permissions": {
    "allow": ["mcp__simple-mcp__read_code", "mcp__simple-mcp__list_files"],
    "deny": ["mcp__simple-mcp__bugdb_update"]
  }
}
```

### Tool Search (Auto-Optimization)

When many MCP tools are configured (>10% of context window), Claude Code activates **Tool Search** automatically. Instead of loading all tool definitions, it uses `MCPSearch` to find relevant tools on demand.

- Reduces context from ~51K tokens to ~8.5K tokens
- Configure: `ENABLE_TOOL_SEARCH=auto` (default), `true`, `false`

### Output Limits

- **Default max:** 25,000 tokens per tool output
- **Warning at:** 10,000 tokens
- **Configure:** `MAX_MCP_OUTPUT_TOKENS=50000`

### Simple MCP Server: Current Tools

| Tool | Description | Read-Only |
|------|-------------|-----------|
| `read_code` | Read Simple source file | Yes |
| `list_files` | List .spl files in directory | Yes |
| `search_code` | Search code patterns (grep) | Yes |
| `file_info` | Get file stats (lines, functions, classes) | Yes |
| `bugdb_get` | Get bug by ID | Yes |
| `bugdb_add` | Add new bug | No |
| `bugdb_update` | Update existing bug | No |

**Location:** `src/app/mcp/main.spl` lines 278-349

---

## 3. Resources

### How Claude Uses Resources

Resources appear in Claude Code's `@` autocomplete menu. Users reference them with `@` mentions:

```
User: Can you analyze @simple-mcp:bugdb://open and prioritize them?

Claude (internally):
1. Fetches resource via resources/read
2. Includes content as context attachment
3. Analyzes and responds
```

**JSON-RPC flow:**

```json
// 1. Claude Code lists resources
{"jsonrpc":"2.0","id":1,"method":"resources/list"}

// 2. Server returns resource catalog
{"jsonrpc":"2.0","id":1,"result":{"resources":[
  {"uri":"project:///info","name":"Project Info","mimeType":"text/plain"},
  {"uri":"bugdb://all","name":"All Bugs","mimeType":"application/json"},
  {"uri":"bugdb://open","name":"Open Bugs","mimeType":"application/json"}
]}}

// 3. Claude Code lists templates for dynamic resources
{"jsonrpc":"2.0","id":2,"method":"resources/templates/list"}

// 4. Server returns URI templates
{"jsonrpc":"2.0","id":2,"result":{"resourceTemplates":[
  {"uriTemplate":"file:///{path}","name":"File Contents","mimeType":"text/plain"},
  {"uriTemplate":"docs:///{path}","name":"Documentation","mimeType":"text/markdown"},
  {"uriTemplate":"symbol:///{name}","name":"Symbol Info","mimeType":"application/json"}
]}}

// 5. Claude Code reads a specific resource
{"jsonrpc":"2.0","id":3,"method":"resources/read",
 "params":{"uri":"bugdb://open"}}

// 6. Server returns resource content
{"jsonrpc":"2.0","id":3,"result":{"contents":[
  {"uri":"bugdb://open","mimeType":"application/json",
   "text":"[{\"id\":\"bug_042\",\"title\":\"Parser crash\",\"severity\":\"P0\"}]"}
]}}
```

### Simple MCP Server: Current Resources

| URI Scheme | Example | Description | Status |
|------------|---------|-------------|--------|
| `project://` | `project:///info` | Project metadata | Complete |
| `file://` | `file:///src/main.spl` | File contents | Complete |
| `symbol://` | `symbol:///parse` | Symbol information | Stub |
| `type://` | `type:///Parser` | Type information | Stub |
| `docs://` | `docs:///guide/syntax` | Documentation | Complete |
| `tree://` | `tree:///src` | Directory tree | Complete |
| `bugdb://` | `bugdb://open` | Bug database queries | Complete |
| `featuredb://` | `featuredb://stats` | Feature database | Complete |
| `testdb://` | `testdb://flaky` | Test database | Complete |

**Location:** `src/app/mcp/resources.spl` (506 lines)

---

## 4. Prompts

### How Claude Uses Prompts

MCP prompts appear as slash commands in Claude Code with `mcp__` prefix:

```
User: /mcp__simple-mcp__generate-tests src/compiler/parser.spl

Claude (internally):
1. Calls prompts/get with name and arguments
2. Receives prompt messages with instructions
3. Follows the instructions to generate tests
```

**JSON-RPC flow:**

```json
// 1. Claude Code lists prompts
{"jsonrpc":"2.0","id":1,"method":"prompts/list"}

// 2. Server returns prompt catalog
{"jsonrpc":"2.0","id":1,"result":{"prompts":[
  {"name":"generate-tests","description":"Generate SSpec tests",
   "arguments":[
     {"name":"target","description":"Function or class to test","required":true},
     {"name":"file","description":"Source file path","required":true}
   ]},
  {"name":"analyze-find-bugs","description":"Find potential bugs",
   "arguments":[
     {"name":"file","description":"File to analyze","required":true}
   ]}
]}}

// 3. Claude Code gets a specific prompt
{"jsonrpc":"2.0","id":2,"method":"prompts/get",
 "params":{"name":"generate-tests","arguments":{"target":"Parser","file":"src/compiler/parser.spl"}}}

// 4. Server returns prompt messages
{"jsonrpc":"2.0","id":2,"result":{
  "description":"Generate SSpec tests for Parser in src/compiler/parser.spl",
  "messages":[
    {"role":"user","content":{"type":"text","text":"Please generate comprehensive SSpec tests for the Parser class in src/compiler/parser.spl.\n\nInstructions:\n1. Read the implementation\n2. Identify edge cases\n3. Write tests covering: positive cases, negative cases, boundary conditions\n4. Use SSpec BDD format (describe/it blocks)\n5. Include both unit and integration tests"}}
  ]
}}
```

### Simple MCP Server: Current Prompts (15)

| Category | Prompt Name | Arguments | Purpose |
|----------|-------------|-----------|---------|
| Refactoring | `refactor-rename` | old_name, new_name, file? | Rename symbol |
| Refactoring | `refactor-extract-function` | code, function_name, file | Extract function |
| Refactoring | `refactor-inline` | name, file | Inline function/variable |
| Code Gen | `generate-tests` | target, file | Generate SSpec tests |
| Code Gen | `generate-trait-impl` | class_name, trait_name, file | Implement trait |
| Code Gen | `generate-constructor` | class_name, file | Generate constructor |
| Docs | `docs-add-docstrings` | target?, file | Add doc comments |
| Docs | `docs-explain-code` | code?, file? | Explain code |
| Docs | `docs-generate-readme` | (none) | Generate README |
| Analysis | `analyze-find-bugs` | file | Find potential bugs |
| Analysis | `analyze-suggest-improvements` | file | Suggest improvements |
| Analysis | `analyze-performance` | file | Performance analysis |

**Location:** `src/app/mcp/prompts.spl` (487 lines)

---

## 5. Progress Notifications

### How It Works (Protocol)

MCP servers can send progress updates during long-running operations:

```json
// Client includes progressToken in request
{"jsonrpc":"2.0","id":5,"method":"tools/call",
 "params":{"name":"run_tests","arguments":{},
  "_meta":{"progressToken":"token-123"}}}

// Server sends progress notifications
{"jsonrpc":"2.0","method":"notifications/progress",
 "params":{"progressToken":"token-123","progress":25,"total":100,"message":"Running test suite 1/4..."}}

{"jsonrpc":"2.0","method":"notifications/progress",
 "params":{"progressToken":"token-123","progress":50,"total":100,"message":"Running test suite 2/4..."}}

// Server sends final tool result
{"jsonrpc":"2.0","id":5,"result":{"content":[{"type":"text","text":"All 4 test suites passed"}]}}
```

### Claude Code Support

**Status: NOT DISPLAYED** (received but not shown to users)

Claude Code receives progress notifications but does not render them in the UI. When an MCP tool runs, Claude Code simply waits for the complete result with no intermediate progress indication.

**Workaround:** Use a two-tool pattern (start_task / get_task_status) for visibility.

**Issue:** [#4157](https://github.com/anthropics/claude-code/issues/4157)

### Simple MCP Server Status

**Not implemented.** Server does not send progress notifications.

**Improvement:** Add progress for long operations (test running, code analysis, database queries).

---

## 6. Logging

### How It Works (Protocol)

MCP servers can send structured log messages:

```json
// Client sets log level
{"jsonrpc":"2.0","id":1,"method":"logging/setLevel",
 "params":{"level":"info"}}

// Server sends log notifications
{"jsonrpc":"2.0","method":"notifications/message",
 "params":{"level":"info","logger":"simple-mcp","data":"Processing query..."}}

{"jsonrpc":"2.0","method":"notifications/message",
 "params":{"level":"warning","logger":"simple-mcp","data":"Database file not found, creating new"}}

{"jsonrpc":"2.0","method":"notifications/message",
 "params":{"level":"error","logger":"simple-mcp","data":"Failed to parse bug record"}}
```

**Log levels:** `debug`, `info`, `notice`, `warning`, `error`, `critical`, `alert`, `emergency`

### Claude Code Support

**Status: NOT DISPLAYED** (received but not shown to users)

Claude Code receives `notifications/message` but does not display them in the UI. The MCP spec says clients "MAY" display log messages -- Claude Code chooses not to.

**Issue:** [#3174](https://github.com/anthropics/claude-code/issues/3174) (closed as NOT_PLANNED)

### Simple MCP Server Status

**Not implemented.** Debug mode writes to stderr only, not via MCP logging protocol.

**Improvement:** Implement `logging/setLevel` handler and send `notifications/message` for server events. Even though Claude Code doesn't display them, other MCP clients may, and it's good protocol compliance.

---

## 7. Sampling

### How It Works (Protocol)

Sampling allows the MCP server to request LLM completions through the client:

```json
// Server sends sampling request to client
{"jsonrpc":"2.0","id":1,"method":"sampling/createMessage",
 "params":{
   "messages":[
     {"role":"user","content":{"type":"text","text":"Summarize this code:\n\nfn parse():\n    ..."}}
   ],
   "maxTokens":500,
   "modelPreferences":{"hints":[{"name":"claude-sonnet-4-5-20250929"}]}
 }}

// Client (Claude) generates completion and returns
{"jsonrpc":"2.0","id":1,"result":{
  "role":"assistant",
  "content":{"type":"text","text":"This function parses..."},
  "model":"claude-sonnet-4-5-20250929",
  "stopReason":"end_turn"
}}
```

### Claude Code Support

**Status: NOT SUPPORTED**

Neither Claude Code nor Claude Desktop supports sampling. This is a highly requested feature.

**Issue:** [#1785](https://github.com/anthropics/claude-code/issues/1785) (77+ upvotes, "actively investigating")

**Workaround:** MCP servers that need LLM inference must make direct API calls.

### Simple MCP Server Status

**Not implemented.** No sampling requests sent.

**Future use case:** Server could use sampling for intelligent code analysis where the server sends code context and receives AI-generated insights.

---

## 8. Elicitation

### How It Works (Protocol)

Elicitation lets the server request structured user input:

```json
// Server sends elicitation request
{"jsonrpc":"2.0","id":1,"method":"elicitation/create",
 "params":{
   "message":"Which bug severity should we filter?",
   "requestedSchema":{
     "type":"object",
     "properties":{
       "severity":{"type":"string","enum":["P0","P1","P2","P3"],
                    "description":"Bug severity level"}
     },
     "required":["severity"]
   }
 }}

// Client shows form to user, returns response
{"jsonrpc":"2.0","id":1,"result":{
  "action":"accept",
  "content":{"severity":"P0"}
}}
```

### Claude Code Support

**Status: NOT SUPPORTED**

Claude Code does not support elicitation. VS Code Copilot supports it since v1.102.

**Issue:** [#2799](https://github.com/anthropics/claude-code/issues/2799) (118+ upvotes)

### Simple MCP Server Status

**Not implemented.**

**Future use case:** Interactive bug triage (server asks user to confirm severity), configuration wizard, debug session setup.

---

## 9. Roots

### How It Works (Protocol)

Roots inform the server about client workspace directories:

```json
// During initialization, client declares roots capability
{"jsonrpc":"2.0","id":1,"method":"initialize",
 "params":{
   "capabilities":{"roots":{"listChanged":true}},
   "clientInfo":{"name":"claude-code","version":"2.1.32"}
 }}

// Server requests root list
{"jsonrpc":"2.0","id":2,"method":"roots/list"}

// Client returns root directories
{"jsonrpc":"2.0","id":2,"result":{
  "roots":[
    {"uri":"file:///home/user/dev/pub/simple","name":"Simple Project"},
    {"uri":"file:///home/user/dev/pub/simple/src","name":"Source Code"}
  ]
}}

// Client notifies when roots change
{"jsonrpc":"2.0","method":"notifications/roots/list_changed"}
```

### Claude Code Support

**Status: SUPPORTED**

Claude Code provides filesystem roots to MCP servers during initialization.

**Claude Desktop:** Does NOT support roots.

### Simple MCP Server Status

**Not implemented.** Server uses `get_current_dir()` instead of querying client roots.

**Improvement:** Use roots from client to determine project boundary instead of relying on cwd.

---

## 10. Tasks

### How It Works (Protocol)

Tasks enable "call-now, fetch-later" for long-running operations:

```json
// 1. Client calls tool, server returns task handle
{"jsonrpc":"2.0","id":1,"method":"tools/call",
 "params":{"name":"run_all_tests","arguments":{}}}

{"jsonrpc":"2.0","id":1,"result":{
  "content":[{"type":"text","text":"Task started"}],
  "_meta":{"task":{"id":"task-abc","status":"running"}}
}}

// 2. Client polls task status
{"jsonrpc":"2.0","id":2,"method":"tasks/get",
 "params":{"id":"task-abc"}}

{"jsonrpc":"2.0","id":2,"result":{
  "id":"task-abc","status":"running","progress":{"current":45,"total":100}
}}

// 3. Client fetches result when complete
{"jsonrpc":"2.0","id":3,"method":"tasks/result",
 "params":{"id":"task-abc"}}

{"jsonrpc":"2.0","id":3,"result":{
  "content":[{"type":"text","text":"100/100 tests passed"}]
}}

// 4. Client can cancel
{"jsonrpc":"2.0","id":4,"method":"tasks/cancel",
 "params":{"id":"task-abc"}}
```

### Claude Code Support

**Status: NOT SUPPORTED** (spec added 2025-11-25, experimental)

### Simple MCP Server Status

**Not implemented.**

**Future use case:** Build system tasks, test execution, coverage generation, code analysis.

---

## 11. Notifications (list_changed)

### How It Works (Protocol)

Servers notify clients when their tool/resource/prompt catalogs change:

```json
// Server added a new tool dynamically
{"jsonrpc":"2.0","method":"notifications/tools/list_changed"}

// Client refreshes tool list
{"jsonrpc":"2.0","id":5,"method":"tools/list"}

// Similarly for resources and prompts
{"jsonrpc":"2.0","method":"notifications/resources/list_changed"}
{"jsonrpc":"2.0","method":"notifications/prompts/list_changed"}
```

### Claude Code Support

**Status: PARTIALLY SUPPORTED**

- `notifications/tools/list_changed` -- Works (refreshes available tools)
- `notifications/prompts/list_changed` -- Buggy (prompts may not update)
- `notifications/resources/list_changed` -- Works

**Issues:** [#2722](https://github.com/anthropics/claude-code/issues/2722), [#4094](https://github.com/anthropics/claude-code/issues/4094)

### Simple MCP Server Status

**Not implemented.** Server has static tool/resource/prompt lists.

**Improvement:** Send notifications when database content changes (e.g., bug added triggers resource list update).

---

## 12. Resource Subscriptions

### How It Works (Protocol)

Clients subscribe to specific resources and receive updates:

```json
// Client subscribes to a resource
{"jsonrpc":"2.0","id":1,"method":"resources/subscribe",
 "params":{"uri":"bugdb://open"}}

// Server acknowledges
{"jsonrpc":"2.0","id":1,"result":{}}

// Later, when resource changes, server notifies
{"jsonrpc":"2.0","method":"notifications/resources/updated",
 "params":{"uri":"bugdb://open"}}

// Client re-reads the resource
{"jsonrpc":"2.0","id":2,"method":"resources/read",
 "params":{"uri":"bugdb://open"}}

// Client unsubscribes
{"jsonrpc":"2.0","id":3,"method":"resources/unsubscribe",
 "params":{"uri":"bugdb://open"}}
```

### Claude Code Support

**Status: NOT SUPPORTED**

Resources are fetched as one-time reads only. No subscription-based updates.

**Issue:** [#7252](https://github.com/anthropics/claude-code/issues/7252) (closed as NOT_PLANNED)

### Simple MCP Server Status

**Not implemented.**

---

## 13. Tool Annotations

### How It Works (Protocol)

Tool annotations provide metadata about tool behavior:

```json
{"jsonrpc":"2.0","id":1,"result":{"tools":[
  {
    "name": "read_code",
    "description": "Read a Simple source file",
    "annotations": {
      "title": "Read Source File",
      "readOnlyHint": true,
      "destructiveHint": false,
      "idempotentHint": true,
      "openWorldHint": false
    },
    "inputSchema": {"type":"object","properties":{"path":{"type":"string"}}}
  },
  {
    "name": "bugdb_update",
    "description": "Update an existing bug",
    "annotations": {
      "title": "Update Bug Record",
      "readOnlyHint": false,
      "destructiveHint": false,
      "idempotentHint": true,
      "openWorldHint": false
    },
    "inputSchema": {"type":"object","properties":{"id":{"type":"string"},"updates":{"type":"string"}}}
  }
]}}
```

| Annotation | Type | Description |
|------------|------|-------------|
| `title` | string | Human-readable display name |
| `readOnlyHint` | bool | Tool only reads data, no side effects |
| `destructiveHint` | bool | Tool may delete or permanently modify data |
| `idempotentHint` | bool | Calling multiple times has same effect as once |
| `openWorldHint` | bool | Tool interacts with external systems |

### Claude Code Support

**Status: SUPPORTED** (uses annotations for permission decisions)

Claude Code uses `readOnlyHint` and `destructiveHint` to inform permission prompts. Read-only tools may be auto-approved more readily.

### Simple MCP Server Status

**Not implemented.** Tools have no annotations.

**Recommended annotations for Simple MCP tools:**

| Tool | readOnly | destructive | idempotent | openWorld |
|------|----------|-------------|------------|-----------|
| `read_code` | true | false | true | false |
| `list_files` | true | false | true | false |
| `search_code` | true | false | true | false |
| `file_info` | true | false | true | false |
| `bugdb_get` | true | false | true | false |
| `bugdb_add` | false | false | false | false |
| `bugdb_update` | false | false | true | false |

---

## 14. Structured Output

### How It Works (Protocol)

Tools can return typed JSON alongside text:

```json
// Tool definition includes outputSchema
{
  "name": "bugdb_get",
  "description": "Get bug by ID",
  "inputSchema": {"type":"object","properties":{"id":{"type":"string"}}},
  "outputSchema": {
    "type": "object",
    "properties": {
      "id": {"type":"string"},
      "title": {"type":"string"},
      "severity": {"type":"string","enum":["P0","P1","P2","P3"]},
      "status": {"type":"string","enum":["open","investigating","confirmed","fixed","closed"]}
    }
  }
}

// Tool result includes structuredContent
{"jsonrpc":"2.0","id":1,"result":{
  "content": [{"type":"text","text":"Bug bug_042: Parser crash on empty input (P0, open)"}],
  "structuredContent": {
    "id": "bug_042",
    "title": "Parser crash on empty input",
    "severity": "P0",
    "status": "open"
  }
}}
```

### Claude Code Support

**Status: SUPPORTED** (spec 2025-03-26+)

Claude can use `structuredContent` for machine-readable processing while displaying `content` text to the user.

### Simple MCP Server Status

**Not implemented.** All tool results are plain text.

**Improvement:** Add `outputSchema` and `structuredContent` to database tools for machine-readable results.

---

## 15. Pagination

### How It Works (Protocol)

Large lists use cursor-based pagination:

```json
// First page
{"jsonrpc":"2.0","id":1,"method":"tools/list"}

{"jsonrpc":"2.0","id":1,"result":{
  "tools": [/* first 50 tools */],
  "nextCursor": "cursor-abc"
}}

// Next page
{"jsonrpc":"2.0","id":2,"method":"tools/list",
 "params":{"cursor":"cursor-abc"}}

{"jsonrpc":"2.0","id":2,"result":{
  "tools": [/* next 50 tools */]
  // No nextCursor = last page
}}
```

### Claude Code Support

**Status: SUPPORTED** (handles pagination automatically)

### Simple MCP Server Status

**Not implemented.** All results returned in single response.

**Improvement:** Add pagination for large resource lists (e.g., `bugdb://all` with hundreds of bugs).

---

## 16. Content Types

### How It Works (Protocol)

Tool results can contain multiple content types:

```json
// Text content
{"type": "text", "text": "Analysis complete"}

// Image content (base64)
{"type": "image", "data": "iVBORw0KGgo...", "mimeType": "image/png"}

// Audio content (base64)
{"type": "audio", "data": "UklGRi4A...", "mimeType": "audio/wav"}

// Embedded resource
{"type": "resource", "resource": {
  "uri": "file:///coverage.html",
  "mimeType": "text/html",
  "text": "<html>..."
}}
```

### Claude Code Support

**Status: SUPPORTED** (text + image; audio support varies)

Claude Code displays text content directly and can process image content (base64-encoded).

### Simple MCP Server Status

**Only text content.** No image/audio/embedded resource support.

**Improvement:** Add image content for coverage reports, directory tree visualizations.

---

## 17. Completions

### How It Works (Protocol)

Auto-completion for prompt and resource arguments:

```json
// Client requests completion for a prompt argument
{"jsonrpc":"2.0","id":1,"method":"completion/complete",
 "params":{
   "ref":{"type":"ref/prompt","name":"generate-tests"},
   "argument":{"name":"file","value":"src/comp"}
 }}

// Server returns suggestions
{"jsonrpc":"2.0","id":1,"result":{
  "completion":{"values":["src/compiler/parser.spl","src/compiler/lexer.spl","src/compiler/hir.spl"],"hasMore":false}
}}
```

### Claude Code Support

**Status: SUPPORTED**

### Simple MCP Server Status

**Not implemented.**

**Improvement:** Add completion for file paths, bug IDs, feature categories.

---

## 18. Transport

### Protocol Message Format

All transports use JSON-RPC 2.0 with Content-Length headers:

```
Content-Length: 123\r\n
\r\n
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{...}}
```

### Transport Options

| Transport | Claude Code | Claude Desktop | Simple MCP |
|-----------|-------------|----------------|------------|
| **stdio** | Supported | Supported | Implemented |
| **Streamable HTTP** | Supported (`--transport http`) | Via Connectors UI | Not implemented |
| **SSE** | Deprecated | Via Connectors UI | Not implemented |

### Claude Code Examples

```bash
# Stdio (default for local)
claude mcp add --transport stdio simple-mcp -- simple mcp server

# HTTP (recommended for remote)
claude mcp add --transport http remote-server https://mcp.example.com/mcp

# SSE (deprecated)
claude mcp add --transport sse legacy-server https://mcp.example.com/sse
```

### Simple MCP Server Status

**Only stdio.** No HTTP or SSE transport.

**Improvement:** Add `simple mcp server --port 8080` for HTTP transport.

---

## 19. Protocol Version

### Version History

| Version | Date | Key Additions |
|---------|------|---------------|
| `2024-11-05` | Nov 2024 | Original MCP release |
| `2025-03-26` | Mar 2025 | Tool annotations, structured output, streamable HTTP |
| `2025-06-18` | Jun 2025 | Elicitation, enhanced OAuth |
| `2025-11-25` | Nov 2025 | Tasks (experimental), sampling with tools, extensions |

### Client Versions

| Client | Protocol Version |
|--------|-----------------|
| Claude Code | `2025-06-18` |
| Claude Desktop | `2025-06-18` |
| **Simple MCP Server** | **`2024-11-05`** (outdated) |

### Initialization Handshake

```json
// Client sends
{"jsonrpc":"2.0","id":1,"method":"initialize",
 "params":{
   "protocolVersion":"2025-06-18",
   "capabilities":{"roots":{"listChanged":true},"sampling":{}},
   "clientInfo":{"name":"claude-code","version":"2.1.32"}
 }}

// Server responds (Simple MCP current)
{"jsonrpc":"2.0","id":1,"result":{
  "protocolVersion":"2024-11-05",
  "capabilities":{"tools":{},"resources":{},"prompts":{}},
  "serverInfo":{"name":"simple-mcp","version":"2.0.0"}
}}
```

**Improvement:** Update to `2025-06-18` to match Claude Code's protocol version.

---

## 20. Feature Support Matrix

| # | Feature | Claude Code | Claude Desktop | Simple MCP | Priority |
|---|---------|-------------|----------------|------------|----------|
| 1 | **Tools** | Supported | Supported | 7 tools | - |
| 2 | **Resources** | Supported (one-time) | Supported | 9 URI schemes | - |
| 3 | **Prompts** | Supported (as `/mcp__`) | Supported | 15 templates | - |
| 4 | **Tool Annotations** | Supported | Unknown | Not impl | P1 (easy) |
| 5 | **Structured Output** | Supported | Unknown | Not impl | P2 |
| 6 | **Progress** | Received, not shown | Unknown | Not impl | P2 |
| 7 | **Logging** | Received, not shown | Unknown | Not impl | P2 |
| 8 | **Sampling** | Not supported | Not supported | Not impl | P3 |
| 9 | **Elicitation** | Not supported | Not supported | Not impl | P3 |
| 10 | **Roots** | Supported | Not supported | Not impl | P2 |
| 11 | **Tasks** | Not supported | Not supported | Not impl | P3 |
| 12 | **list_changed** | Partial (tools ok) | Unknown | Not impl | P2 |
| 13 | **Subscriptions** | Not supported | Not supported | Not impl | P3 |
| 14 | **Pagination** | Supported | Unknown | Not impl | P2 |
| 15 | **Content Types** | Text + Image | Text + Image | Text only | P2 |
| 16 | **Completions** | Supported | Unknown | Not impl | P3 |
| 17 | **Streamable HTTP** | Supported | Via UI | Not impl | P2 |
| 18 | **Protocol Version** | 2025-06-18 | 2025-06-18 | 2024-11-05 | P1 |

### Priority Legend

- **P1 (Quick Win):** Small effort, high impact for Claude compatibility
- **P2 (Medium):** Moderate effort, improves protocol compliance
- **P3 (Future):** Claude doesn't support yet, or large effort

### Recommended Implementation Order

```
1. Protocol version update → 2025-06-18     (P1, ~10 lines)
2. Tool annotations                          (P1, ~50 lines)
3. Logging support                           (P2, ~100 lines)
4. Pagination                                (P2, ~150 lines)
5. Structured output for DB tools            (P2, ~200 lines)
6. Roots integration                         (P2, ~100 lines)
7. list_changed notifications                (P2, ~100 lines)
8. Completions (file paths, IDs)             (P3, ~150 lines)
9. Progress notifications                    (P2, ~150 lines)
10. Content types (image support)            (P2, ~100 lines)
11. Streamable HTTP transport                (P2, ~800 lines)
12. Tasks support                            (P3, ~500 lines)
13. Sampling support                         (P3, ~300 lines)
14. Elicitation support                      (P3, ~300 lines)
```

---

## 21. Claude Code Built-in Tools

Claude Code ships with ~20 built-in tools that work without any MCP server configuration. These are the default capabilities available in every Claude Code session.

### File Operations

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **Read** | Read files with multimodal support | `file_path`, `offset?`, `limit?`, `pages?` | Images, PDFs, Jupyter notebooks. Default 2000 lines, `cat -n` format |
| **Write** | Create or overwrite files | `file_path`, `content` | Enforces read-before-write validation |
| **Edit** | Exact string replacements | `file_path`, `old_string`, `new_string`, `replace_all?` | Fails if `old_string` is not unique (unless `replace_all=true`) |
| **MultiEdit** | Multiple edits in one file atomically | Same as Edit, but batched | All succeed or none apply |
| **NotebookEdit** | Edit Jupyter notebook cells | `notebook_path`, `new_source`, `cell_id?`, `cell_type?`, `edit_mode?` | Replace, insert, delete. 0-indexed cells |

### Search and Discovery

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **Glob** | Fast file pattern matching | `pattern`, `path?` | Standard glob syntax (`**/*.js`). Results sorted by modification time |
| **Grep** | Content search (built on ripgrep) | `pattern`, `path?`, `output_mode?`, `glob?`, `type?`, `-i?`, `-n?`, `-A/-B/-C?`, `multiline?` | Three modes: `content`, `files_with_matches` (default), `count` |

### Execution

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **Bash** | Execute shell commands | `command`, `description?`, `timeout?`, `run_in_background?` | Persistent working directory. Default 120s timeout, max 600s. 30K char output limit |
| **TaskOutput** | Get output from background tasks | `task_id`, `block?`, `timeout?` | Works with background shells and subagents |
| **TaskStop** | Terminate background tasks | `task_id` | Stops running background processes |

### Web Operations

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **WebFetch** | Fetch URL and extract info via AI | `url`, `prompt` | HTML-to-markdown conversion. 15-minute cache. Fails on authenticated URLs |
| **WebSearch** | Search the web | `query`, `allowed_domains?`, `blocked_domains?` | US only. Returns links as markdown. Must include Sources section |

### Agent and Task Management

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **Task** | Launch specialized sub-agents | `prompt`, `description`, `subagent_type` | Up to 10 concurrent. Types: Explore, Plan, general-purpose, Bash, etc. |
| **Skill** | Execute user-defined skills | `skill`, `args?` | Loaded from `.claude/skills/` and `~/.claude/skills/` |

**Built-in subagent types:**

| Type | Model | Tools | Use Case |
|------|-------|-------|----------|
| `Explore` | Haiku | Read-only (Glob, Grep, Read) | Fast codebase search. Supports `quick`, `medium`, `very thorough` |
| `Plan` | Inherits | Read-only | Research during plan mode |
| `general-purpose` | Inherits | All tools | Complex multi-step operations |
| `Bash` | Inherits | Bash only | Terminal commands in separate context |
| `claude-code-guide` | Haiku | Web tools | Questions about Claude Code features |

**Constraints:** Subagents CANNOT spawn other subagents (no nesting). Custom subagents via `.claude/agents/` or `~/.claude/agents/`.

### Planning and Tracking

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **TaskCreate** | Create structured task lists | `subject`, `description`, `activeForm?` | For multi-step session tracking |
| **TaskUpdate** | Update task status/details | `taskId`, `status?`, `subject?`, `description?` | Status: `pending` -> `in_progress` -> `completed` |
| **TaskList** | List all tasks | (none) | Shows IDs, status, owners, blockers |
| **TaskGet** | Get full task details | `taskId` | Returns description, dependencies |
| **ExitPlanMode** | Exit plan mode with implementation plan | (none) | Only for code implementation planning |
| **EnterPlanMode** | Enter planning mode | (none) | For non-trivial implementation tasks |

### User Interaction

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **AskUserQuestion** | Ask structured questions | `questions` (1-4) | 2-4 options per question. "Other" auto-added |

### IDE Integration (VS Code / JetBrains only)

| Tool | Description | Parameters | Notes |
|------|-------------|------------|-------|
| **getDiagnostics** | Get language diagnostics | `uri?` | Type errors, warnings from IDE |
| **executeCode** | Run Python in Jupyter kernel | `code` | State persists across calls |

### Relevance to Simple MCP Server

These built-in tools show the patterns Claude expects. When designing Simple MCP server tools:

- **Naming:** Claude's built-in tools use PascalCase (`WebFetch`) or camelCase (`getDiagnostics`). Simple MCP uses snake_case (`read_code`) -- both patterns work.
- **Descriptions:** Claude expects clear, specific descriptions. Include what the tool does AND when to use it.
- **Input schemas:** Match Claude's pattern of `required` + `optional` parameters with clear types.
- **Output size:** Keep tool outputs under 10,000 tokens (warning threshold). Use pagination for large results.

---

## 22. Claude Code as MCP Server

### `claude mcp serve`

Claude Code can run as an MCP server itself, exposing its tools to other applications:

```bash
# Start Claude Code as a stdio MCP server
claude mcp serve
```

### Tools Exposed

When running as an MCP server, Claude Code exposes:

| Tool Name | Maps To | Description |
|-----------|---------|-------------|
| `Read` (View) | Read tool | Read file contents |
| `Write` | Write tool | Create/overwrite files |
| `Edit` | Edit tool | Targeted file edits |
| `Bash` | Bash tool | Shell command execution |
| `LS` | Bash ls | List directory contents |
| `GrepTool` | Grep tool | Search file contents |
| `GlobTool` | Glob tool | Find files by pattern |
| `Replace` | Edit tool | Find and replace operations |
| `dispatch_agent` | Task tool | Delegate to sub-agents |

**Important limitations:**
- **No MCP passthrough:** MCP servers that Claude Code connects to are NOT exposed to clients
- **No resources or prompts:** Only tools are exposed
- **Headless mode:** No interactive permission prompts (client must handle confirmation)

### Configuration for Claude Desktop

```json
{
  "mcpServers": {
    "claude-code": {
      "type": "stdio",
      "command": "claude",
      "args": ["mcp", "serve"],
      "env": {}
    }
  }
}
```

If `claude` is not in PATH, use the full path:

```bash
which claude  # Find full path
```

```json
{
  "mcpServers": {
    "claude-code": {
      "type": "stdio",
      "command": "/full/path/to/claude",
      "args": ["mcp", "serve"],
      "env": {}
    }
  }
}
```

### Security Model

- **Transport:** Stdio only -- no network exposure
- **Authentication:** None required -- security through process isolation
- **Access:** Only processes that launch the server can connect
- **One process per client:** No shared state between clients

### Read-Only Restriction Example

Restrict exposed tools via permissions:

```json
{
  "permissions": {
    "allow": ["Read(**)", "Glob(**)", "Grep(**)"],
    "deny": ["Write(**)", "Edit(**)", "Bash(**)", "Replace(**)"]
  }
}
```

### Relevance to Simple MCP Server

`claude mcp serve` provides file operation tools. The Simple MCP server provides **domain-specific** tools (bug DB, feature DB, test DB, code analysis). They complement each other:

```json
{
  "mcpServers": {
    "claude-code": {
      "command": "claude", "args": ["mcp", "serve"]
    },
    "simple-mcp": {
      "command": "simple", "args": ["mcp", "server"]
    }
  }
}
```

---

## 23. Tool Search (MCPSearch) Internals

### Activation

MCPSearch activates automatically when MCP tool descriptions exceed 10% of the context window. Instead of loading all MCP tools upfront, tools are deferred and discovered on demand.

### How It Works

```
1. Claude Code starts with many MCP servers configured
2. Total tool definitions would consume >10% of context
3. MCPSearch is enabled -- tools are deferred
4. Claude uses MCPSearch to find relevant tools when needed
5. Only discovered tools are loaded into context
6. MCP tools work normally from user perspective
```

### Configuration

| `ENABLE_TOOL_SEARCH` | Behavior |
|-----------------------|----------|
| `auto` (default) | Activates at 10% context threshold |
| `auto:<N>` | Custom threshold (e.g., `auto:5` for 5%) |
| `true` | Always enabled |
| `false` | Disabled, all MCP tools loaded upfront |

```bash
# Custom threshold
ENABLE_TOOL_SEARCH=auto:5 claude

# Disable
ENABLE_TOOL_SEARCH=false claude
```

**Disable via settings:**

```json
{
  "permissions": {
    "deny": ["MCPSearch"]
  }
}
```

### Model Requirements

- **Supported:** Sonnet 4+, Opus 4+ (models with `tool_reference` block support)
- **Not supported:** Haiku models

### Tips for MCP Server Authors

Write clear `instructions` fields in your server info so Claude knows when to search for your tools:

```json
{
  "serverInfo": {
    "name": "simple-mcp",
    "version": "2.0.0"
  },
  "instructions": "Search for Simple MCP tools when the user asks about Simple language source code, bugs, tests, or features. Provides code reading, bug tracking, feature tracking, and test result tools."
}
```

### Simple MCP Server Status

**Not sending instructions.** Add server instructions to help MCPSearch discover Simple MCP tools effectively.

---

## 24. Permission Prompt Tool

### What It Does

The `--permission-prompt-tool` flag delegates permission decisions to an external MCP tool, replacing interactive permission prompts. This enables custom security policies and automated approval workflows.

### Usage

```bash
claude -p --permission-prompt-tool <mcp_tool_name> "your task"
```

### Permission Resolution Layers

```
Layer 1: Static ALLOW rules from settings.json
Layer 2: Static DENY rules from settings.json
Layer 3: Dynamic resolution via --permission-prompt-tool MCP call
```

Only Layer 3 (the MCP tool) is called when Layers 1 and 2 don't match.

### Response Format

The MCP tool must return JSON:

**Allow response:**
```json
{
  "behavior": "allow",
  "updatedInput": { }
}
```

**Deny response:**
```json
{
  "behavior": "deny",
  "message": "Reason for denial"
}
```

The `updatedInput` field is optional but allows the permission server to modify tool input parameters before execution.

### Example: Custom Permission Server

```bash
# Start with permission delegation
claude -p --permission-prompt-tool mcp__my-policy__check_permission "refactor the parser"
```

The permission tool receives:
- The action/command Claude Code wants to execute
- Context about the operation being requested

### Relevance to Simple MCP Server

Could implement a permission-checking tool in Simple MCP server for organizational policies:

```simple
# Hypothetical: simple mcp server with permission tool
tool "check_permission":
    description: "Evaluate permission request against project policy"
    input: {action: text, context: text}
    output: {behavior: text, message: text?}
```

---

## 25. MCP Resource Access Tools

### Built-in Resource Tools

Claude Code provides two built-in tools for accessing MCP server resources:

| Tool | Description | Parameters |
|------|-------------|------------|
| **ListMcpResourcesTool** | List available resources from MCP servers | `server?` (optional filter) |
| **ReadMcpResourceTool** | Read a specific resource | `server` (required), `uri` (required) |

### Usage Pattern

```
User: @simple-mcp:bugdb://open

Claude (internally):
1. Uses ListMcpResourcesTool to discover resources from "simple-mcp"
2. Uses ReadMcpResourceTool with server="simple-mcp", uri="bugdb://open"
3. Resource content is attached to the conversation context
4. Claude analyzes and responds
```

### `@` Mention Autocomplete

Type `@` in Claude Code to see available resources from all connected MCP servers:

```
> @simple-mcp:bugdb://open        # Bug database
> @simple-mcp:file:///src/main.spl # Source file
> @simple-mcp:testdb://flaky       # Flaky tests

# Multiple resource references in one prompt
> Compare @simple-mcp:bugdb://open with @simple-mcp:testdb://failed
```

Resources are fuzzy-searchable in the `@` mention autocomplete menu.

### MCP Output Limits

| Setting | Default | Description |
|---------|---------|-------------|
| Warning threshold | 10,000 tokens | Shows warning when exceeded |
| Max output | 25,000 tokens | Hard limit per tool output |
| `MAX_MCP_OUTPUT_TOKENS` | 25,000 | Environment variable to override |

```bash
# Increase limit for large resources
MAX_MCP_OUTPUT_TOKENS=50000 claude
```

---

## 26. Built-in Slash Commands

### MCP-Related Commands

| Command | Purpose |
|---------|---------|
| `/mcp` | Manage MCP server connections and OAuth authentication |
| `/init` | Initialize project (can create `.mcp.json`) |

### MCP Prompt Commands

MCP server prompts are available as slash commands with the format:

```
/mcp__<server-name>__<prompt-name> [arguments]
```

**Examples with Simple MCP server:**

```
/mcp__simple-mcp__generate-tests src/compiler/parser.spl
/mcp__simple-mcp__analyze-find-bugs src/app/mcp/main.spl
/mcp__simple-mcp__docs-explain-code src/compiler/lexer.spl
/mcp__simple-mcp__refactor-rename old_name new_name
```

### Custom Slash Commands

Create custom commands as markdown files:

```
.claude/commands/          # Project-scoped
~/.claude/commands/        # User-scoped
```

Each `.md` file becomes a `/command-name`. Can reference `$ARGUMENTS` for user input.

### All Built-in Slash Commands

| Command | Purpose |
|---------|---------|
| `/clear` | Clear conversation history |
| `/compact` | Compact conversation with optional focus |
| `/config` | Open Settings interface |
| `/context` | Visualize current context usage |
| `/copy` | Copy last response to clipboard |
| `/cost` | Show token usage statistics |
| `/debug` | Troubleshoot current session |
| `/doctor` | Check Claude Code installation health |
| `/exit` | Exit the REPL |
| `/export` | Export conversation to file/clipboard |
| `/help` | Get usage help |
| `/init` | Initialize project with CLAUDE.md |
| `/mcp` | Manage MCP servers and OAuth |
| `/memory` | Edit CLAUDE.md memory files |
| `/model` | Select or change AI model |
| `/permissions` | View or update permissions |
| `/plan` | Enter plan mode |
| `/resume` | Resume a conversation |
| `/rewind` | Rewind conversation and/or code |
| `/stats` | Visualize usage, history, streaks |
| `/tasks` | List and manage background tasks |
| `/theme` | Change color theme |
| `/vim` | Enable vim-style editing |
| `/agents` | Manage AI subagents |

---

## 27. Managed MCP Configuration

### For Organizations

Two options for centralized MCP server control:

### Option 1: Exclusive Control (`managed-mcp.json`)

Deploy a fixed set of MCP servers. Users cannot add or modify servers.

**Locations:**
- macOS: `/Library/Application Support/ClaudeCode/managed-mcp.json`
- Linux/WSL: `/etc/claude-code/managed-mcp.json`
- Windows: `C:\Program Files\ClaudeCode\managed-mcp.json`

```json
{
  "mcpServers": {
    "company-internal": {
      "type": "stdio",
      "command": "/usr/local/bin/company-mcp-server",
      "args": ["--config", "/etc/company/mcp-config.json"]
    },
    "simple-mcp": {
      "command": "simple",
      "args": ["mcp", "server"]
    }
  }
}
```

### Option 2: Allowlists / Denylists

Allow users to add servers within policy constraints:

```json
{
  "allowedMcpServers": [
    {"serverName": "simple-mcp"},
    {"serverName": "github"},
    {"serverCommand": ["npx", "-y", "@modelcontextprotocol/server-filesystem"]},
    {"serverUrl": "https://mcp.company.com/*"}
  ],
  "deniedMcpServers": [
    {"serverName": "dangerous-server"},
    {"serverUrl": "https://*.untrusted.com/*"}
  ]
}
```

**Rules:**
- `allowedMcpServers: undefined` -- No restrictions (default)
- `allowedMcpServers: []` -- Complete lockdown
- Denylist takes absolute precedence over allowlist
- Matching: by name (`serverName`), exact command (`serverCommand`), or URL pattern (`serverUrl` with `*` wildcards)
- Options 1 and 2 can be combined

### Relevance to Simple MCP Server

Organizations deploying Simple MCP server can:

1. **Managed deployment:** Include `simple-mcp` in `managed-mcp.json` for standardized access
2. **Allowlist:** Add `{"serverName": "simple-mcp"}` or `{"serverCommand": ["simple", "mcp", "server"]}` to allow users to configure it
3. **Restrict tools:** Combine with permissions to limit which Simple MCP tools are available

---

## References

- [Claude Code MCP Documentation](https://code.claude.com/docs/en/mcp)
- [MCP Specification (2025-06-18)](https://modelcontextprotocol.io/specification/2025-06-18)
- [MCP Specification (2025-11-25)](https://spec.modelcontextprotocol.io)
- [Rust SDK (rmcp)](https://github.com/modelcontextprotocol/rust-sdk)
- [Python SDK (mcp)](https://github.com/modelcontextprotocol/python-sdk)
- [Claude Desktop MCP Setup](https://support.claude.com/en/articles/10949351)
- [Apify MCP Client Capabilities](https://github.com/apify/mcp-client-capabilities)
- [Claude Code Sampling Request (#1785)](https://github.com/anthropics/claude-code/issues/1785)
- [Claude Code Elicitation Request (#2799)](https://github.com/anthropics/claude-code/issues/2799)
- [Claude Code Progress Display (#4157)](https://github.com/anthropics/claude-code/issues/4157)
- [Claude Code Logging Display (#3174)](https://github.com/anthropics/claude-code/issues/3174)
