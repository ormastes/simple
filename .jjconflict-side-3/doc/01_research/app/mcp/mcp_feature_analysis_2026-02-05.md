# MCP Feature Analysis: Rust SDK, Python SDK vs Simple MCP Server

**Date:** 2026-02-05
**Status:** Research Complete
**Purpose:** Gap analysis between official MCP SDKs and Simple's MCP implementation

---

## 1. Official SDK Overview

### 1.1 Rust SDK (`rmcp` v0.14.0)

**Repository:** https://github.com/modelcontextprotocol/rust-sdk
**Crate:** https://crates.io/crates/rmcp
**Docs:** https://docs.rs/rmcp
**Stars:** ~3k | **Contributors:** 130+ | **Releases:** 52+

**ServerHandler trait (25 methods):**

| Category | Methods | Description |
|----------|---------|-------------|
| Core | `get_info`, `initialize`, `ping` | Server identity and lifecycle |
| Tools | `list_tools`, `call_tool` | Tool enumeration and invocation |
| Resources | `list_resources`, `list_resource_templates`, `read_resource`, `subscribe`, `unsubscribe` | Resource management |
| Prompts | `list_prompts`, `get_prompt` | Prompt templates |
| Logging | `set_level` | Log level control |
| Completion | `complete` | Auto-completion for arguments |
| Tasks | `enqueue_task`, `list_tasks`, `get_task_info`, `get_task_result`, `cancel_task` | Long-running operations (experimental) |
| Custom | `on_custom_request` | Extension point |
| Notifications | `on_cancelled`, `on_progress`, `on_initialized`, `on_roots_list_changed`, `on_custom_notification` | Event handling |

**ClientHandler trait (14 methods):**

| Category | Methods | Description |
|----------|---------|-------------|
| Sampling | `create_message` | LLM sampling via server request |
| Roots | `list_roots` | Root resource listing |
| Elicitation | `create_elicitation` | Structured user input gathering |
| Custom | `on_custom_request` | Extension point |
| Notifications | `on_cancelled`, `on_progress`, `on_logging_message`, `on_resource_updated`, `on_resource_list_changed`, `on_tool_list_changed`, `on_prompt_list_changed`, `on_custom_notification` | Event handling |

**Transports:**
- `transport-io` (Stdio)
- `transport-sse` (Server-Sent Events)
- `transport-streamable-http-client` / `transport-streamable-http-server` (Streamable HTTP)
- `transport-child-process` (Subprocess)

**Key Features:**
- `#[tool]` macro for zero-boilerplate tool definitions
- `#[tool_box]` / `tool_box!()` for auto-routing
- `Json<T>` wrapper for typed JSON responses with auto-generated schemas
- `IntoContents` trait for custom content conversion
- `Arc<Mutex<T>>` pattern for stateful servers
- Pagination support (`PaginatedRequestParams`, `Cursor`)
- Content types: Text, Image, Audio, EmbeddedResource, JSON
- Elicitation schemas: Boolean, Integer, Number, String, Enum (single/multi select)
- Task lifecycle (SEP-1686): Queued → Running → Completed/Failed/Cancelled
- Tool annotations for behavior hints
- OAuth 2.0 via `auth` feature flag (RFC 8414, OpenID Connect)
- Tower middleware compatibility via `tower` feature
- Role-based type system (`RoleClient`/`RoleServer`) prevents protocol violations at compile time
- Blanket impls: `()`, `Box<T>`, `Arc<T>` all implement `ClientHandler`/`ServerHandler`

**Feature Flags (18):**

| Flag | Purpose |
|------|---------|
| `server` / `client` | Core role implementations |
| `macros` | `#[tool]`, `#[tool_router]` (default on) |
| `transport-io` | Stdio transport |
| `transport-child-process` | Subprocess transport |
| `transport-streamable-http-server` | HTTP server (axum/hyper) |
| `transport-streamable-http-client` | HTTP client |
| `transport-async-rw` | Generic async I/O |
| `auth` | OAuth 2.0 authentication |
| `elicitation` | User input gathering |
| `tower` | Tower middleware |
| `schemars` | JSON Schema generation |
| `base64` | Base64 encoding |

**Note:** SSE transport was **removed** in v0.11.0 in favor of Streamable HTTP.

**Recent Releases:**

| Version | Date | Key Changes |
|---------|------|-------------|
| 0.14.0 | Jan 2025 | Decoupled request payload, task model fix |
| 0.13.0 | Jan 2025 | Task support (SEP-1686), `close()`, `StateStore`, blanket impls |
| 0.12.0 | Dec 2024 | Custom requests/notifications, URL-based client IDs |
| 0.11.0 | Dec 2024 | **SSE removed**, `_meta` field, OutputSchema validation |

---

### 1.2 Python SDK (`mcp` v1.26.0)

**Repository:** https://github.com/modelcontextprotocol/python-sdk
**PyPI:** https://pypi.org/project/mcp/
**Docs:** https://modelcontextprotocol.github.io/python-sdk/
**Stars:** ~21.5k | **Python:** >= 3.10 | **License:** MIT
**Latest:** v1.26.0 (Jan 24, 2026) | **v2 pre-alpha** on `main` branch (Q1 2026)

**Two-Tier Architecture:**
- **High-Level:** `FastMCP` (decorator-based, recommended)
- **Low-Level:** `Server` class (full protocol control)

**FastMCP High-Level API:**

```python
from mcp.server.fastmcp import FastMCP

mcp = FastMCP("Demo", json_response=True)

@mcp.tool()
def add(a: int, b: int) -> int:
    """Add two numbers"""
    return a + b

@mcp.resource("greeting://{name}")
def get_greeting(name: str) -> str:
    """Get a personalized greeting"""
    return f"Hello, {name}!"

@mcp.prompt()
def review_code(code: str) -> str:
    """Review code for issues"""
    return f"Please review this code:\n{code}"

mcp.run(transport="streamable-http")
```

**Key Features:**

| Feature | Description |
|---------|-------------|
| Decorators | `@mcp.tool()`, `@mcp.resource()`, `@mcp.prompt()` |
| Auto Schema | Generates JSON Schema from Python type annotations (Pydantic, TypedDict, dataclass) |
| Context Object | `ctx.report_progress()`, `ctx.read_resource()`, `ctx.info()`, `ctx.debug()` |
| Transports | Stdio, SSE (deprecated), **Streamable HTTP** (recommended), WebSocket (`mcp[ws]`) |
| Tool Annotations | `readOnlyHint`, `destructiveHint`, `title` |
| Structured Output | `outputSchema` + `structuredContent` in `CallToolResult` |
| Async Support | Both sync and async tools |
| Lifespan | `@asynccontextmanager` for startup/shutdown lifecycle |
| Logging | `send_log_message()` with levels (debug, info, warning, error, critical) |
| Progress | `send_progress_notification()` with current/total |
| Image Content | `ImageContent` with base64 encoding |
| Tasks | Experimental (2025-11-25 spec) - "call-now, fetch-later" |
| Sampling | Server requests LLM completions through client (`create_message`) |
| Elicitation | Server requests structured user input (schema-validated) |
| Notifications | Resource/tool/prompt list changed |
| Subscriptions | `subscribe`/`unsubscribe` for resource updates |
| OAuth 2.1 | Token verification for Streamable HTTP |
| ASGI Mounting | `app.mount("/mcp", mcp.http_app())` for FastAPI/Starlette |
| Client API | Full `ClientSession` for consuming MCP servers |

**Context Object (injected via type annotation):**
```python
from mcp.server.fastmcp import Context

@mcp.tool()
async def process(data: str, ctx: Context) -> str:
    await ctx.info("Processing started")
    await ctx.report_progress(0.5, 1.0)
    result = await ctx.read_resource("config://settings")
    db = ctx.request_context.lifespan_context.db  # lifespan state
    return "Done"
```

**Transport Comparison:**

| Transport | Status | Use Case |
|-----------|--------|----------|
| Stdio | Stable | Local CLI tools, Claude Desktop |
| SSE | **Deprecated** (2025-03-26) | Legacy HTTP streaming |
| Streamable HTTP | **Recommended** | Production, single endpoint, bidirectional |
| WebSocket | Optional (`mcp[ws]`) | Alternative streaming |

**Recent Releases:**

| Version | Date | Key Changes |
|---------|------|-------------|
| 1.26.0 | Jan 2026 | Resource/ResourceTemplate metadata backport |
| 1.25.0 | Dec 2025 | New branching strategy (main=v2, v1.x=stable) |
| 1.23.0 | Dec 2025 | Sampling with tools, Tasks, SSE polling, URL elicitation, JWT/Basic auth |

**Note:** FastMCP 2.0 (`fastmcp` on PyPI, by jlowin) is a separate extended framework with enterprise auth, server composition, and OpenAPI generation. The official `mcp` package is sufficient for most use cases.

---

## 2. Simple MCP Server - Current State

**Location:** `src/app/mcp/`
**Total:** ~2,837 lines across 10 modules
**Protocol Version:** `2024-11-05`

### 2.1 What We Have

| Feature | Status | Details |
|---------|--------|---------|
| JSON-RPC 2.0 | ✅ Complete | `main.spl` (729 lines) |
| Stdio Transport | ✅ Complete | Content-Length header protocol |
| 9 Resource URI Schemes | ✅ Complete | file, symbol, type, docs, tree, bugdb, featuredb, testdb, project |
| 6 Resource Templates | ✅ Complete | Dynamic URI patterns |
| 15 Prompt Templates | ✅ Complete | Refactoring, generation, docs, analysis |
| 7 Tools | ✅ Complete | read_code, list_files, search_code, file_info, bugdb_get/add/update |
| Bug DB Integration | ✅ Complete | CRUD via `bugdb_resource.spl` |
| Feature DB Integration | ✅ Complete | Read via `featuredb_resource.spl` |
| Test DB Integration | ✅ Complete | Read/write via `testdb_resource.spl` |
| Document Editor | ✅ Complete | `editor.spl` (164 lines) |
| Debug Sessions | ✅ Complete | `session.spl` (127 lines) |
| Error Handling | ✅ Basic | JSON-RPC error codes (-32601, -32602) |
| CLI Modes | ✅ Complete | server, read, expand, json, search |

### 2.2 What We DON'T Have

| Feature | Priority | Effort | Description |
|---------|----------|--------|-------------|
| **Streamable HTTP Transport** | P1-High | Large | Modern transport, replaces SSE, single endpoint |
| **Tasks (Experimental)** | P1-High | Large | Long-running operation tracking |
| **Progress Notifications** | P1-High | Medium | Real-time progress updates to client |
| **Logging Support** | P1-High | Small | `set_level` + `logging/message` notifications |
| **Tool Annotations** | P2-Medium | Small | `readOnlyHint`, `destructiveHint`, `title` |
| **Structured Output** | P2-Medium | Medium | `outputSchema` + `structuredContent` in CallToolResult |
| **Pagination** | P2-Medium | Medium | `cursor` for large resource/tool/prompt lists |
| **Sampling / create_message** | P2-Medium | Medium | Server-initiated LLM completion requests |
| **Elicitation** | P2-Medium | Medium | Structured user input gathering |
| **Resource Subscriptions** | P2-Medium | Medium | `subscribe`/`unsubscribe` + update notifications |
| **Image/Audio Content** | P3-Low | Small | Base64-encoded media in tool results |
| **Roots** | P3-Low | Small | Client-provided root resource directories |
| **Completions** | P3-Low | Small | Auto-completion for prompt/resource arguments |
| **Custom Requests/Notifications** | P3-Low | Small | Extension point for protocol extensions |
| **Protocol Version Update** | P1-High | Small | Upgrade from `2024-11-05` to `2025-11-25` |

---

## 3. Gap Analysis Detail

### 3.1 Protocol Version (P1-Critical)

**Current:** `2024-11-05`
**Latest:** `2025-11-25`

The project is **2 major protocol revisions behind**. The 2025-03-26 revision added:
- Tool annotations
- Streamable HTTP transport (replacing SSE)
- `readOnlyHint`, `destructiveHint`

The 2025-11-25 revision added:
- Tasks (experimental)
- Better OAuth
- Extensions mechanism
- Improved agentic workflows

**Action:** Update `protocolVersion` in `main.spl` line 265 and implement corresponding features.

### 3.2 Transport Layer (P1-High)

**Current:** Stdio only
**Missing:** Streamable HTTP (the new standard)

Streamable HTTP provides:
- Single HTTP endpoint (POST + GET)
- Bidirectional communication
- Server-initiated notifications on same connection
- SSE streaming over HTTP
- Stateless mode (`stateless_http=True`, `json_response=True`)

**Impact:** Without Streamable HTTP, the server cannot be deployed as a web service. It can only run as a local subprocess.

**Effort:** Large (~500-800 lines). Requires HTTP server infrastructure.

### 3.3 Tasks (P1-High)

**Current:** Not implemented
**Spec:** Experimental in 2025-11-25

Tasks enable "call-now, fetch-later" semantics:
1. Client calls a tool
2. Server returns a task handle immediately
3. Client polls task status later
4. Client fetches result when complete
5. Client can cancel running tasks

**Required methods:**
- `enqueue_task(params) -> CreateTaskResult`
- `list_tasks() -> ListTasksResult`
- `get_task_info(params) -> GetTaskInfoResult`
- `get_task_result(params) -> TaskResult`
- `cancel_task(params) -> ()`

**Use cases for Simple:** Long-running compilation, test execution, code analysis.

### 3.4 Progress Notifications (P1-High)

**Current:** Not implemented
**Impact:** Clients have no visibility into long operations

Required:
- `ProgressToken` in request meta
- `notifications/progress` with `progress`, `total`, `message`
- Server sends progress during tool execution

### 3.5 Logging (P1-High)

**Current:** Debug mode writes to stderr
**Missing:** Proper MCP logging protocol

Required:
- `logging/setLevel` request handler
- `notifications/message` with level (debug, info, warning, error, critical)
- Log messages sent to client as notifications

**Effort:** Small (~100 lines). Simple to implement.

### 3.6 Tool Annotations (P2-Medium)

**Current:** Tools have no behavioral hints
**Missing:** Metadata about tool safety and behavior

```json
{
  "name": "read_code",
  "annotations": {
    "title": "Read Source File",
    "readOnlyHint": true,
    "destructiveHint": false,
    "idempotentHint": true,
    "openWorldHint": false
  }
}
```

**Effort:** Small (~50 lines). Add annotations to existing tool definitions.

### 3.7 Structured Output (P2-Medium)

**Current:** All tool results are plain text
**Missing:** `outputSchema` + `structuredContent`

Allows tools to return typed JSON objects alongside text:
```json
{
  "content": [{"type": "text", "text": "Found 5 bugs"}],
  "structuredContent": {
    "total": 5,
    "critical": 2,
    "bugs": [...]
  }
}
```

**Use cases:** Database queries, code analysis results, test reports.

### 3.8 Symbol/Type Resources (Implementation Gap)

**Current:** Stub implementations (return placeholder text)
**Required:** Actual compiler introspection

These resources are listed but return dummy data:
- `symbol://{name}` - Should return definition location, type, references
- `type://{name}` - Should return type definition, fields, methods

**Action:** Integrate with compiler's symbol table and type system.

### 3.9 JSON Handling (Architecture Gap)

**Current:** Manual string concatenation (`jo2`, `jp`, `js` helper functions)
**Problem:** Fragile, hard to maintain, potential escaping bugs

```simple
# Current approach (main.spl)
val text_obj = jo2(jp("type", js("text")), jp("text", js(content)))
val result = jo1(jp("content", "[" + text_obj + "]"))
```

**Recommendation:** Use a proper JSON builder library or enhance `resource_utils.spl`'s `JsonBuilder`.

---

## 4. Feature Comparison Matrix

| Feature | Rust SDK (rmcp) | Python SDK (mcp) | Simple MCP | Gap |
|---------|----------------|-----------------|------------|-----|
| **Protocol Version** | 2025-11-25 | 2025-11-25 | 2024-11-05 | **2 versions behind** |
| **Stdio Transport** | ✅ | ✅ | ✅ | None |
| **SSE Transport** | ✅ | ✅ (deprecated) | ❌ | Minor (deprecated) |
| **Streamable HTTP** | ✅ | ✅ | ❌ | **Major** |
| **WebSocket** | ❌ | ✅ (optional) | ❌ | Minor |
| **Tools** | ✅ (macro-based) | ✅ (decorator) | ✅ (manual) | API ergonomics |
| **Tool Annotations** | ✅ | ✅ | ❌ | **Medium** |
| **Structured Output** | ✅ | ✅ | ❌ | **Medium** |
| **Resources** | ✅ | ✅ | ✅ (9 schemes) | None |
| **Resource Templates** | ✅ | ✅ | ✅ (6 templates) | None |
| **Resource Subscriptions** | ✅ | ✅ | ❌ | Medium |
| **Prompts** | ✅ | ✅ | ✅ (15 templates) | None |
| **Sampling** | ✅ | ✅ | ❌ | Medium |
| **Elicitation** | ✅ | ✅ | ❌ | Medium |
| **Tasks** | ✅ (experimental) | ✅ (experimental) | ❌ | **Major** |
| **Progress** | ✅ | ✅ | ❌ | **Major** |
| **Logging** | ✅ | ✅ | ❌ (stderr only) | **Medium** |
| **Pagination** | ✅ | ✅ | ❌ | Medium |
| **Roots** | ✅ | ✅ | ❌ | Minor |
| **Completions** | ✅ | ✅ | ❌ | Minor |
| **Image Content** | ✅ | ✅ | ❌ | Minor |
| **Audio Content** | ✅ | ✅ | ❌ | Minor |
| **Custom Requests** | ✅ | ✅ | ❌ | Minor |
| **OAuth / Auth** | N/A (transport) | ✅ (OAuth 2.1) | ❌ | Low (stdio only) |
| **ASGI Mounting** | N/A | ✅ (FastAPI) | ❌ | Low (needs HTTP first) |
| **Lifespan Mgmt** | ✅ | ✅ (asynccontextmanager) | ❌ | Medium |
| **Client API** | ✅ | ✅ (ClientSession) | ❌ | Medium |
| **Error Handling** | ✅ (typed) | ✅ (typed) | ✅ (basic codes) | Improve |
| **Content Types** | Text, Image, Audio, Embedded, JSON | Text, Image, Embedded | Text only | **Medium** |

### Score Summary

| Category | Simple MCP | Max Possible |
|----------|-----------|--------------|
| Core Protocol | 4/6 | 67% |
| Tools | 3/5 | 60% |
| Resources | 4/5 | 80% |
| Prompts | 3/3 | 100% |
| Advanced Features | 0/11 | 0% |
| **Overall** | **14/30** | **47%** |

---

## 5. Improvement Recommendations

### Phase 1: Quick Wins (1-2 days)

1. **Update Protocol Version** → `2025-11-25`
   - File: `main.spl` line 265
   - Change `protocolVersion` from `"2024-11-05"` to `"2025-11-25"`

2. **Add Logging Support**
   - Implement `logging/setLevel` handler
   - Send `notifications/message` for log events
   - Replace stderr debug output with proper MCP logging
   - ~100 lines

3. **Add Tool Annotations**
   - Add `annotations` field to each tool in `tools/list` response
   - `read_code`: `readOnlyHint: true`
   - `list_files`: `readOnlyHint: true`
   - `search_code`: `readOnlyHint: true`
   - `file_info`: `readOnlyHint: true`
   - `bugdb_add`: `destructiveHint: false` (creates, doesn't destroy)
   - `bugdb_update`: `destructiveHint: false`
   - ~50 lines

4. **Add Progress Notifications**
   - Add `ProgressToken` handling to request context
   - Send `notifications/progress` during long operations
   - ~150 lines

### Phase 2: Medium Effort (3-5 days)

5. **Structured Output for Database Tools**
   - Add `outputSchema` to database tools
   - Return `structuredContent` alongside text content
   - Benefits: Machine-readable results for AI clients
   - ~200 lines

6. **Pagination Support**
   - Add `cursor` parameter to list methods
   - Return `nextCursor` when results exceed page size
   - Apply to: `tools/list`, `resources/list`, `prompts/list`
   - ~150 lines

7. **Resource Subscriptions**
   - Implement `resources/subscribe` and `resources/unsubscribe`
   - Track subscribers per resource URI
   - Send `notifications/resources/updated` on changes
   - ~200 lines

8. **Image Content Support**
   - Add `ImageContent` type (base64 + mimeType)
   - Useful for: directory tree visualization, coverage reports
   - ~100 lines

9. **Improve JSON Handling**
   - Replace manual string concatenation with proper builder
   - Extend `resource_utils.spl`'s `JsonBuilder` for all JSON output
   - ~300 lines (refactoring)

### Phase 3: Large Effort (1-2 weeks)

10. **Tasks Support**
    - New module: `src/app/mcp/tasks.spl`
    - Task lifecycle management (create, poll, cancel)
    - Integration with build system and test runner
    - ~500 lines

11. **Streamable HTTP Transport**
    - New module: `src/app/mcp/http_transport.spl`
    - Single HTTP endpoint (POST + GET)
    - SSE streaming for notifications
    - Requires HTTP server (SFFI wrapper needed)
    - ~800 lines

12. **Sampling Support**
    - Server-to-client LLM completion requests
    - Requires client handler infrastructure
    - ~300 lines

13. **Elicitation Support**
    - Structured user input gathering
    - Schema builders for form-like interactions
    - ~300 lines

14. **Implement Symbol/Type Resources**
    - Integrate with compiler's symbol table
    - Requires compiler API access
    - ~400 lines

---

## 6. Comparison with Rust/Python SDK Patterns

### 6.1 API Ergonomics

**Rust SDK approach (macro-based):**
```rust
#[tool(description = "Read a source file")]
async fn read_code(&self, path: String) -> Result<String, McpError> {
    std::fs::read_to_string(path).map_err(|e| McpError::invalid_request(e.to_string()))
}
```

**Python SDK approach (decorator-based):**
```python
@mcp.tool()
def read_code(path: str) -> str:
    """Read a source file"""
    return open(path).read()
```

**Simple's current approach (manual):**
```simple
# Tool defined as JSON string in tools/list response
# Handler is a big match statement in handle_tool_call()
```

**Recommendation:** Consider creating a Simple-native tool registration API:
```simple
# Hypothetical future API
val server = McpServer("simple-mcp", version: "3.0.0")

server.tool("read_code", description: "Read a source file",
    annotations: ToolAnnotations(read_only: true)):
    \params:
        val path = params.get("path")
        file_read(path)

server.resource("file://{path}", description: "File contents"):
    \uri:
        file_read(extract_path(uri))

server.run(transport: "stdio")
```

### 6.2 Content Type System

**Rust SDK:** `Content` enum with `Text`, `Image`, `Audio`, `EmbeddedResource`
**Python SDK:** `TextContent`, `ImageContent`, `EmbeddedResource` classes
**Simple:** Plain text strings only

**Recommendation:** Add a `Content` variant type:
```simple
enum Content:
    Text(text: text)
    Image(data: text, mime_type: text)  # base64
    Resource(uri: text, content: text)
```

### 6.3 Error Handling

**Rust SDK:** `McpError` with typed error codes, `Result<T, McpError>` pattern
**Python SDK:** Exception-based with automatic conversion
**Simple:** Manual JSON error construction

**Recommendation:** Create `McpError` struct:
```simple
struct McpError:
    code: i64
    message: text

val METHOD_NOT_FOUND = McpError(code: -32601, message: "Method not found")
val INVALID_PARAMS = McpError(code: -32602, message: "Invalid params")
val INTERNAL_ERROR = McpError(code: -32603, message: "Internal error")
```

---

## 7. Strengths of Simple's MCP Implementation

Despite the gaps, Simple's MCP server has several strengths:

1. **Rich Database Integration** - 3 domain databases (Bug, Feature, Test) with CRUD operations. Neither official SDK provides this level of domain integration out-of-the-box.

2. **Comprehensive Prompt Library** - 15 prompt templates covering refactoring, code generation, documentation, and analysis. This is more than most MCP server examples.

3. **Document Editor** - Built-in document editing with version tracking and transactional semantics. Unique feature.

4. **Debug Session Management** - Multi-target debugging support (interpreter, SMF, native). Not found in any standard MCP server.

5. **Multiple CLI Modes** - Server, read, expand, json, search modes provide flexibility beyond pure MCP protocol.

6. **Self-Hosting** - Entire server is written in Simple, demonstrating the language's capability for real-world applications.

---

## 8. Recommended Roadmap

```
Phase 1 (Quick Wins) ─── 1-2 days
├── Protocol version update (2025-11-25)
├── Logging support (notifications/message)
├── Tool annotations (readOnly, destructive hints)
└── Progress notifications

Phase 2 (Core Features) ─── 3-5 days
├── Structured output for tools
├── Pagination for list endpoints
├── Resource subscriptions
├── Image content support
└── JSON handling refactor

Phase 3 (Advanced) ─── 1-2 weeks
├── Tasks (experimental)
├── Streamable HTTP transport
├── Sampling support
├── Elicitation support
└── Symbol/Type resource implementation

Phase 4 (DX Improvements) ─── 1-2 weeks
├── Declarative tool registration API
├── Content type system
├── Typed error handling
└── MCP server test framework
```

**Priority Order:** Phase 1 → Phase 2 → Phase 3 → Phase 4

---

## 9. References

- [MCP Specification (2025-11-25)](https://spec.modelcontextprotocol.io)
- [MCP Blog: November 2025 Spec Release](http://blog.modelcontextprotocol.io/posts/2025-11-25-first-mcp-anniversary/)
- [Rust SDK (rmcp)](https://github.com/modelcontextprotocol/rust-sdk)
- [Python SDK (mcp)](https://github.com/modelcontextprotocol/python-sdk)
- [rmcp API Docs](https://docs.rs/rmcp)
- [Python SDK Docs](https://modelcontextprotocol.github.io/python-sdk/)
- [FastMCP Documentation](https://gofastmcp.com/)
- [MCP Transports Specification](https://modelcontextprotocol.io/specification/2025-03-26/basic/transports)
- [Coder's Guide to rmcp](https://hackmd.io/@Hamze/S1tlKZP0kx)
- [MCP Tasks: Game-Changer for Long-Running Operations](https://dev.to/gregory_dickson_6dd6e2b55/mcp-gets-tasks-a-game-changer-for-long-running-ai-operations-2kel)
