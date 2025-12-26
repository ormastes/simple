# MCP (Model Context Protocol) Library

A reusable library for building Model Context Protocol servers in Simple language. This library provides a generic protocol implementation that can be extended to support any programming language or tool.

## Architecture

```
mcp/
├── core/              # Generic MCP library (reusable for any language)
│   ├── protocol.spl   # JSON-RPC messages, Resources, Tools, Prompts
│   ├── server.spl     # Generic MCP server with tool dispatch
│   ├── provider.spl   # ResourceProvider interface
│   └── transport.spl  # Transport abstraction (stdio, TCP, mock)
│
├── simple_lang/       # Simple language implementation (example)
│   ├── types.spl      # Simple-specific types (Symbol, BlockMark, etc.)
│   ├── parser.spl     # Parse Simple code and extract symbols
│   ├── formatter.spl  # Format symbols as MCP text
│   └── provider.spl   # SimpleLangProvider implementation
│
└── examples/          # Templates for creating your own provider
    └── template_provider.spl
```

## Quick Start

### For End Users - Using Simple Language MCP

```simple
use mcp.simple_lang.*

# Create Simple language provider
provider = SimpleLangProvider.new("./my_project")

# Register source files
source = "pub class User:\n    name: String"
provider.register_simple_file("user.spl", source)

# List resources
resources = provider.list_resources()

# Read resource in MCP format
contents = provider.read_resource("file://user.spl")
println(contents.text)
# Output: C> pub class User { … }
```

### For Developers - Building Your Own MCP Server

```simple
use mcp.core.*

# 1. Implement ResourceProvider for your language
pub class MyLanguageProvider:
    pub base: BaseProvider
    
    pub fn new(root_path: String) -> MyLanguageProvider:
        return MyLanguageProvider:
            base: BaseProvider.new(root_path)

impl ResourceProvider for MyLanguageProvider:
    fn list_resources(self) -> List[Resource]:
        # Return your language's resources
        return []
    
    fn read_resource(self, uri: String) -> ResourceContents:
        # Format your language's code
        text = "# Formatted code for: " + uri
        return ResourceContents.new(uri, "text/x-my-lang", text)

# 2. Create MCP server
provider = MyLanguageProvider.new(".")
server = McpServer.new("My Language MCP", "1.0.0", provider)

# 3. Register custom tools
tool = Tool.new("analyze", "Analyze code")
handler = create_text_tool("analyze", "Analyze code", fn(args) -> String:
    return "Analysis result"
)
server.register_tool(tool, handler)

# 4. Run server with transport
transport = StdioTransport.new()
while transport.is_alive():
    request_opt = transport.read_message()
    if request_opt.is_some():
        response = server.handle_request(request_opt.unwrap())
        transport.write_response(response)
```

## Core API Reference

### Protocol Types (`core/protocol.spl`)

**JSON-RPC Messages:**
- `JsonRpcRequest` - Request message
- `JsonRpcResponse` - Success response
- `JsonRpcError` - Error response
- `ErrorObject` - Error details

**MCP Types:**
- `Resource` - Represents a code resource (file, symbol, etc.)
- `Tool` - Represents an executable tool
- `Prompt` - Represents a prompt template
- `ResourceContents` - Contents of a resource
- `ToolResult` - Result of tool execution
- `ContentBlock` - Text/Image/Resource content

**Example:**
```simple
# Create a resource
resource = Resource.new(
    "file://main.spl",
    "main.spl",
    "text/x-simple"
)

# Create a tool
tool = Tool.new(
    "format_code",
    "Format code according to style guide"
)
```

### Server (`core/server.spl`)

**McpServer:**
- `new(name, version, provider)` - Create server
- `register_tool(tool, handler)` - Register custom tool
- `handle_request(request)` - Process JSON-RPC request

**ToolHandler:**
- `new(tool, execute_fn)` - Create tool handler
- `execute(arguments)` - Execute tool with arguments

**Helper:**
- `create_text_tool(name, description, handler)` - Create simple text tool

**Example:**
```simple
# Create server
provider = MyProvider.new(".")
server = McpServer.new("My MCP Server", "1.0.0", provider)

# Register tool
search_tool = Tool.new("search", "Search code")
search_handler = create_text_tool("search", "Search", fn(args) -> String:
    query = args.get("query")
    return "Results for: " + query
)
server.register_tool(search_tool, search_handler)
```

### Provider Interface (`core/provider.spl`)

**ResourceProvider Trait:**
```simple
pub trait ResourceProvider:
    fn list_resources(self) -> List[Resource]
    fn read_resource(self, uri: String) -> ResourceContents
    fn search_resources(self, query: String) -> List[Resource]
```

**BaseProvider:**
- `new(root_path)` - Create base provider
- `add_resource(resource)` - Register resource
- `get_resource(uri)` - Get resource by URI

**Built-in Providers:**
- `FileProvider` - File-based resources
- `SymbolProvider` - Symbol-based resources (for code navigation)

### Transport (`core/transport.spl`)

**Transport Trait:**
```simple
pub trait Transport:
    fn read_message(self) -> Option[JsonRpcRequest]
    fn write_response(self, response: JsonRpcResponse)
    fn is_alive(self) -> bool
```

**Built-in Transports:**
- `StdioTransport` - Stdio communication (standard for MCP)
- `TcpTransport` - TCP socket communication
- `MockTransport` - In-memory testing

## Simple Language Implementation

The `simple_lang/` directory provides a complete reference implementation for Simple language:

### Symbol Types (`simple_lang/types.spl`)

- `BlockMark` - Block mark notation (C>, F>, T>, P>, V•)
- `SymbolKind` - Class, Function, Trait, etc.
- `Symbol` - Symbol information
- `McpOutput` - Output format

### Parser (`simple_lang/parser.spl`)

- `parse_file(source)` - Extract symbols from Simple source
- `parse_class()`, `parse_function()`, `parse_trait()`, `parse_pointcut()`
- `filter_public_symbols()` - Keep only public symbols
- `find_symbol()`, `find_symbol_at_line()` - Symbol lookup

### Formatter (`simple_lang/formatter.spl`)

- `format_symbols()` - Generate MCP text
- `format_collapsed_symbol()` - Compact view
- `format_expanded_symbol()` - Full view
- `to_json()` - JSON output

### Provider (`simple_lang/provider.spl`)

- `SimpleLangProvider` - ResourceProvider implementation
- `register_simple_file()` - Register Simple source file
- `create_simple_tools()` - Create Simple-specific tools

## Creating Your Own Language Support

1. **Copy the template:**
   ```bash
   cp simple/std_lib/src/mcp/examples/template_provider.spl my_lang_provider.spl
   ```

2. **Implement ResourceProvider:**
   ```simple
   impl ResourceProvider for MyLangProvider:
       fn list_resources(self) -> List[Resource]:
           # Parse your language files
           # Extract symbols/definitions
           # Return as Resource list
       
       fn read_resource(self, uri: String) -> ResourceContents:
           # Format code in MCP style
           # Return collapsed outline by default
   ```

3. **Create language-specific tools:**
   ```simple
   # Tool: Format code
   format_tool = Tool.new("format", "Format code")
   format_handler = create_text_tool("format", "Format", fn(args) -> String:
       code = args.get("code")
       return my_language_formatter(code)
   )
   server.register_tool(format_tool, format_handler)
   ```

4. **Test with MockTransport:**
   ```simple
   # Create test request
   request = JsonRpcRequest.new(1, "resources/list", {})
   
   # Create mock transport
   transport = MockTransport.new([request])
   
   # Process
   server.handle_request(request)
   ```

## Supported MCP Methods

| Method | Description | Handler |
|--------|-------------|---------|
| `initialize` | Initialize connection | Built-in |
| `ping` | Health check | Built-in |
| `resources/list` | List all resources | `provider.list_resources()` |
| `resources/read` | Read resource | `provider.read_resource()` |
| `tools/list` | List available tools | Server tools registry |
| `tools/call` | Execute tool | Registered tool handler |

## Examples

### Example 1: Rust Language MCP Provider

```simple
use mcp.core.*

pub class RustProvider:
    pub base: BaseProvider
    
    pub fn parse_rust_file(self, source: String):
        # Parse Rust syntax
        # Extract structs, impls, fns, etc.
        pass

impl ResourceProvider for RustProvider:
    fn read_resource(self, uri: String) -> ResourceContents:
        # Format Rust code in MCP style:
        # S> pub struct User { … }
        # I> impl User { … }
        # F> pub fn new() { … }
        pass
```

### Example 2: Python Language MCP Provider

```simple
pub class PythonProvider:
    pub base: BaseProvider
    
    pub fn parse_python_file(self, source: String):
        # Parse Python syntax
        # Extract classes, defs, etc.
        pass

impl ResourceProvider for PythonProvider:
    fn read_resource(self, uri: String) -> ResourceContents:
        # Format Python code in MCP style:
        # C> class User: …
        # F> def login(self, name): …
        pass
```

### Example 3: Multi-Language MCP Server

```simple
# Support multiple languages in one server
pub class MultiLangProvider:
    pub simple_provider: SimpleLangProvider
    pub rust_provider: RustProvider
    pub python_provider: PythonProvider
    
    pub fn route_by_extension(self, uri: String) -> ResourceContents:
        if uri.ends_with(".spl"):
            return self.simple_provider.read_resource(uri)
        elif uri.ends_with(".rs"):
            return self.rust_provider.read_resource(uri)
        elif uri.ends_with(".py"):
            return self.python_provider.read_resource(uri)
        else:
            return ResourceContents.new(uri, "text/plain", "# Unsupported")
```

## Best Practices

1. **Use URI schemes consistently:**
   - `file://path/to/file.spl` - Source files
   - `symbol://file.spl#SymbolName` - Specific symbols
   - `project://ProjectName` - Project-level resources

2. **Provide collapsed view by default:**
   - Show public API outline first
   - Let users expand specific symbols on demand
   - Include virtual information (traits, coverage, etc.)

3. **Make tools specific to your language:**
   - `format_code` - Format according to style guide
   - `find_references` - Find symbol usage
   - `suggest_refactor` - Language-specific refactoring

4. **Test with MockTransport before stdio:**
   - Easier to debug
   - Can write unit tests
   - No I/O dependencies

## File Locations

- Core library: `simple/std_lib/src/mcp/core/`
- Simple implementation: `simple/std_lib/src/mcp/simple_lang/`
- Examples: `simple/std_lib/src/mcp/examples/`
- Tests: `simple/std_lib/test/unit/mcp/`

## Contributing

To add support for a new language:

1. Create `my_lang/` directory under `mcp/`
2. Implement ResourceProvider
3. Add tests in `test/unit/mcp/my_lang/`
4. Document in this README
5. Submit PR

## License

Part of the Simple language standard library.

## See Also

- [MCP Specification](../../doc/spec/basic_mcp.md)
- [Implementation Report](../../doc/report/MCP_IMPLEMENTATION_SUMMARY_2025-12-26.md)
- [Simple Language Documentation](../../doc/)
