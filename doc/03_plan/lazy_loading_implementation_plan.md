# Lazy Handler Loading Implementation Plan

## Goal
Implement lazy handler loading to reduce startup memory footprint and improve scalability for 100+ tools.

## Constraint: Runtime Parser Limitations
- ❌ Cannot dynamically `import(module_path)` at runtime
- ❌ Module closures broken (can't access module-level vars from imported fns)
- ✅ CAN use conditional imports based on static paths
- ✅ CAN defer handler initialization until first use

## Approach: Conditional Group Loading

Instead of true dynamic loading, we'll use **handler groups** that load on first category access:

```
Tool Categories:
- fileio: simple_read, simple_check, simple_symbols, simple_status
- edit: simple_edit, simple_multi_edit, simple_run
- vcs: simple_diff, simple_log, simple_squash, simple_new
- debug: debug_create_session, debug_step, debug_eval, etc.
- debug_log: debug_log_enable, debug_log_disable, etc.
```

**Loading Strategy:**
1. Startup: Register handler metadata only (no imports)
2. First call in category: Import entire category module
3. Subsequent calls: Use cached handler functions
4. Track loaded categories to avoid re-importing

## Implementation Phases

### Phase 1: Handler Registry with Metadata (1 hour)

Create `src/mcp_lib/lazy_registry.spl`:

```simple
# Handler metadata (no function reference)
class HandlerMetadata:
    name: text
    category: text
    module_path: text
    function_name: text

# Registry state
var HANDLER_METADATA: [HandlerMetadata] = []
var LOADED_CATEGORIES: [text] = []
var CACHED_HANDLERS: [CachedHandler] = []  # After loading

class CachedHandler:
    name: text
    handler_fn: fn(text, text) -> text  # (id, body) -> response

# Register handler metadata (no imports yet)
fn register_handler(name: text, category: text, module: text, fn_name: text):
    HANDLER_METADATA.push(HandlerMetadata(
        name: name,
        category: category,
        module_path: module,
        function_name: fn_name
    ))

# Check if category is loaded
fn is_category_loaded(category: text) -> bool:
    for cat in LOADED_CATEGORIES:
        if cat == category:
            return true
    false

# Find cached handler
fn get_cached_handler(name: text) -> fn(text, text) -> text?:
    for handler in CACHED_HANDLERS:
        if handler.name == name:
            return Some(handler.handler_fn)
    nil
```

### Phase 2: Category Loaders (1 hour)

Create category-specific loader functions:

```simple
# src/mcp_lib/category_loaders.spl

# Load fileio category
fn load_fileio_handlers():
    use app.mcp.diag_read_tools.{handle_simple_read, handle_simple_check, handle_simple_symbols, handle_simple_status}

    register_cached("simple_read", handle_simple_read)
    register_cached("simple_check", handle_simple_check)
    register_cached("simple_symbols", handle_simple_symbols)
    register_cached("simple_status", handle_simple_status)

    mark_category_loaded("fileio")

# Load edit category
fn load_edit_handlers():
    use app.mcp.diag_edit_tools.{handle_simple_edit, handle_simple_multi_edit, handle_simple_run}

    register_cached("simple_edit", handle_simple_edit)
    register_cached("simple_multi_edit", handle_simple_multi_edit)
    register_cached("simple_run", handle_simple_run)

    mark_category_loaded("edit")

# ... similar for vcs, debug, debug_log
```

### Phase 3: Lazy Dispatch (30 min)

Update bootstrap to use lazy loading:

```simple
# src/app/mcp/bootstrap/main_lazy.spl

use mcp_lib.lazy_registry.{register_handler, get_cached_handler, is_category_loaded}
use mcp_lib.category_loaders.{load_fileio_handlers, load_edit_handlers, load_vcs_handlers, load_debug_handlers, load_debug_log_handlers}

fn init_handler_registry():
    # Register metadata only (no imports)
    register_handler("simple_read", "fileio", "app.mcp.diag_read_tools", "handle_simple_read")
    register_handler("simple_check", "fileio", "app.mcp.diag_read_tools", "handle_simple_check")
    # ... register all 27 handlers

fn dispatch_tool_lazy(id: text, tool_name: text, body: text) -> text:
    # Try cached handler first
    val cached = get_cached_handler(tool_name)
    match cached:
        Some(fn): return fn(id, body)
        nil: pass

    # Load category on-demand
    val category = get_tool_category(tool_name)
    if not is_category_loaded(category):
        load_category(category)

    # Try again after loading
    val loaded = get_cached_handler(tool_name)
    match loaded:
        Some(fn): fn(id, body)
        nil: make_error_response(id, -32601, "Handler not found: " + tool_name)

fn load_category(category: text):
    if category == "fileio":
        load_fileio_handlers()
    elif category == "edit":
        load_edit_handlers()
    elif category == "vcs":
        load_vcs_handlers()
    elif category == "debug":
        load_debug_handlers()
    elif category == "debug_log":
        load_debug_log_handlers()
```

### Phase 4: Fallback to Eager Loading (30 min)

**Issue:** Runtime limitations may prevent lazy loading from working.

**Solution:** Add eager loading fallback:

```simple
# Bootstrap with fallback
fn start_server_with_lazy_loading(debug: bool):
    init_handler_registry()

    # Try lazy dispatch
    var use_lazy = true

    while running:
        val line = read_stdin_message()
        if line == "":
            running = false
        else:
            val method = extract_json_string_v2(line, "method")
            val id = extract_json_value(line, "id")

            if method == "tools/call":
                val tool_name = extract_nested_string(line, "params", "name")

                var response = ""
                if use_lazy:
                    # Try lazy loading
                    response = dispatch_tool_lazy(id, tool_name, line)
                    if response.contains("Handler not found"):
                        # Lazy failed, fall back to eager
                        use_lazy = false
                        load_all_handlers()
                        response = dispatch_tool_eager(id, tool_name, line)
                else:
                    # Eager loading
                    response = dispatch_tool_eager(id, tool_name, line)

                write_stdout_message(response)
```

## Expected Performance

### Startup Comparison

| Approach | Startup Time | Memory | First Call |
|----------|--------------|--------|------------|
| **Current (Eager)** | ~600ms | High (all handlers) | ~50ms |
| **Lazy Loading** | ~200ms | Low (metadata only) | ~150ms (load + execute) |
| **Lazy + Cache** | ~200ms | Medium (loaded only) | ~50ms (cached) |

### Memory Savings

Assuming each handler module is ~50KB parsed:
- Eager: 27 handlers × 50KB = 1.35MB
- Lazy: Only used handlers loaded
- Example: If only 5 tools used → 5 × 50KB = 250KB (5x reduction)

## Testing Strategy

### Phase 5: Tests (1 hour)

1. **Registry Tests:**
   - Metadata registration
   - Category tracking
   - Handler caching

2. **Loader Tests:**
   - Category loading works
   - Handlers cached correctly
   - Re-loading is safe (no-op)

3. **Dispatch Tests:**
   - Lazy dispatch loads on-demand
   - Cached dispatch is fast
   - Fallback to eager works

4. **Performance Tests:**
   - Startup time < 300ms
   - First call overhead < 200ms
   - Cached calls < 50ms

## Implementation Order

1. **Phase 1:** Handler registry with metadata (1 hr)
2. **Phase 2:** Category loaders (1 hr)
3. **Phase 3:** Lazy dispatch logic (30 min)
4. **Phase 4:** Eager fallback (30 min)
5. **Phase 5:** Tests and validation (1 hr)

**Total:** 4 hours

## Risks & Mitigations

**Risk 1: Runtime can't import conditionally**
- Mitigation: Eager loading fallback
- Impact: Falls back to current behavior

**Risk 2: Module closures prevent caching**
- Mitigation: Test early, adjust architecture
- Impact: May need to keep handlers in-process

**Risk 3: Complexity not worth memory savings**
- Mitigation: Measure actual memory usage first
- Impact: Defer if savings < 50%

## Success Criteria

✅ Startup time < 300ms (vs 600ms eager)
✅ Memory usage reduced by >30% for typical usage
✅ All 27 handlers still accessible
✅ Fallback to eager if lazy fails
✅ Tests passing for all scenarios

## Decision Point

**Before implementing, measure:**
1. Current memory usage of eager loading
2. Typical tool usage patterns (how many tools used per session?)
3. Actual startup time difference

**Proceed if:**
- Memory savings > 500KB
- Startup improvement > 200ms
- OR: Expected to scale beyond 50 tools

**Defer if:**
- Memory usage acceptable
- Startup time meets goals
- Tool count stays < 30
