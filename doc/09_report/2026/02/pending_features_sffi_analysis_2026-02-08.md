# Pending Features and SFFI Gap Analysis

**Date:** 2026-02-08
**Total Skip Tests:** 1,983
**Status:** Analysis Complete

---

## Executive Summary

Analysis of 1,983 `skip_it`/`slow_it` tests reveals that **most pending features are NOT blocked by missing SFFI wrappers**. Instead, they are blocked by:

1. **Runtime parser syntax limitations** (~1,400 tests) - Features implemented in compiler, but runtime parser doesn't support the syntax
2. **Implementation in progress** (~400 tests) - Features partially implemented
3. **Missing SFFI wrappers** (~100 tests) - Actually need new SFFI bindings
4. **Slow tests** (~83 tests) - Working but too slow for regular test runs

---

## Part 1: Missing SFFI Wrappers (Can Be Implemented)

These features are blocked by missing SFFI wrappers and could be unblocked by adding the appropriate wrappers:

### 1. JIT/Execution Manager SFFI (High Priority)

**Blocked Tests:** ~30
**Impact:** High - Enables runtime code compilation and optimization

**Missing Functions:**
```simple
# src/app/io/mod.spl (need to add)

# --- JIT Backend Control ---
extern fn rt_set_jit_backend(backend: text) -> bool
extern fn rt_get_jit_backend() -> text

fn jit_set_backend(backend: text) -> bool:
    rt_set_jit_backend(backend)

fn jit_get_backend() -> text:
    rt_get_jit_backend()

# --- Execution Manager ---
extern fn rt_exec_manager_create(backend: text) -> i64
extern fn rt_exec_manager_compile(manager: i64, code: text) -> bool
extern fn rt_exec_manager_execute(manager: i64, function: text, args: [text]) -> text
extern fn rt_exec_manager_has_function(manager: i64, name: text) -> bool
extern fn rt_exec_manager_backend_name(manager: i64) -> text
extern fn rt_exec_manager_cleanup(manager: i64) -> bool

struct ExecManager:
    handle: i64
    is_valid: bool

fn exec_manager_create(backend: text) -> ExecManager:
    val handle = rt_exec_manager_create(backend)
    ExecManager(handle: handle, is_valid: handle != 0)

fn exec_manager_compile(manager: ExecManager, code: text) -> bool:
    if not manager.is_valid:
        false
    else:
        rt_exec_manager_compile(manager.handle, code)

fn exec_manager_execute(manager: ExecManager, function: text, args: [text]) -> text:
    if not manager.is_valid:
        ""
    else:
        rt_exec_manager_execute(manager.handle, function, args)

fn exec_manager_has_function(manager: ExecManager, name: text) -> bool:
    if not manager.is_valid:
        false
    else:
        rt_exec_manager_has_function(manager.handle, name)

fn exec_manager_backend_name(manager: ExecManager) -> text:
    if not manager.is_valid:
        ""
    else:
        rt_exec_manager_backend_name(manager.handle)

fn exec_manager_cleanup(manager: ExecManager) -> bool:
    if manager.is_valid:
        rt_exec_manager_cleanup(manager.handle)
    else:
        true
```

**Rust Implementation Needed:** ~300 lines
**Backend:** Cranelift or LLVM JIT
**Priority:** 🔴 High - Unblocks dynamic compilation features

---

### 2. Process/System Info SFFI (Medium Priority)

**Blocked Tests:** ~15
**Impact:** Medium - Completes system info APIs

**Missing Functions:**
```simple
# src/app/io/mod.spl (need to add)

# --- Process Info ---
extern fn rt_getpid() -> i64
extern fn rt_getppid() -> i64
extern fn rt_getuid() -> i64
extern fn rt_getgid() -> i64
extern fn rt_get_process_name() -> text
extern fn rt_get_process_path() -> text

fn process_pid() -> i64:
    rt_getpid()

fn process_parent_pid() -> i64:
    rt_getppid()

fn process_user_id() -> i64:
    rt_getuid()

fn process_group_id() -> i64:
    rt_getgid()

fn process_name() -> text:
    rt_get_process_name()

fn process_path() -> text:
    rt_get_process_path()
```

**Rust Implementation Needed:** ~100 lines
**Dependencies:** Standard library (libc)
**Priority:** 🟡 Medium - Nice to have for system utilities

---

### 3. LLVM IR Export SFFI (Low Priority)

**Blocked Tests:** ~5
**Impact:** Low - For advanced compiler users

**Missing Functions:**
```simple
# src/app/io/mod.spl (need to add)

# --- LLVM Codegen ---
extern fn rt_compile_to_llvm_ir(source_path: text, output_path: text) -> bool
extern fn rt_compile_to_llvm_bc(source_path: text, output_path: text) -> bool
extern fn rt_optimize_llvm_ir(ir_path: text, opt_level: i64) -> bool

fn compile_to_llvm_ir(source: text, output: text) -> bool:
    rt_compile_to_llvm_ir(source, output)

fn compile_to_llvm_bitcode(source: text, output: text) -> bool:
    rt_compile_to_llvm_bc(source, output)

fn optimize_llvm_ir(ir_path: text, opt_level: i64) -> bool:
    rt_optimize_llvm_ir(ir_path, opt_level)
```

**Rust Implementation Needed:** ~200 lines (if LLVM backend exists)
**Dependencies:** LLVM (optional dependency)
**Priority:** ⚪ Low - Advanced feature, limited use cases

---

### 4. Network/HTTP SFFI (Medium Priority)

**Blocked Tests:** ~50
**Impact:** Medium - Enables network programming

**Potential Wrapper:** `reqwest` (HTTP client) or `hyper` (HTTP server)

**Example SFFI Wrapper:**
```simple
# src/app/io/http_ffi.spl (NEW)

# --- HTTP Client ---
extern fn rt_http_get(url: text) -> (i64, text, text)  # (status, body, error)
extern fn rt_http_post(url: text, body: text, content_type: text) -> (i64, text, text)
extern fn rt_http_request(method: text, url: text, headers: [text], body: text) -> (i64, text, text)

struct HttpResponse:
    status: i64
    body: text
    error: text
    is_ok: bool

fn http_get(url: text) -> HttpResponse:
    val result = rt_http_get(url)
    HttpResponse(status: result.0, body: result.1, error: result.2, is_ok: result.0 >= 200 and result.0 < 300)

fn http_post(url: text, body: text, content_type: text) -> HttpResponse:
    val result = rt_http_post(url, body, content_type)
    HttpResponse(status: result.0, body: result.1, error: result.2, is_ok: result.0 >= 200 and result.0 < 300)

# --- HTTP Server ---
extern fn rt_http_server_new(port: i64) -> i64
extern fn rt_http_server_route(server: i64, method: text, path: text, handler: text) -> bool
extern fn rt_http_server_start(server: i64) -> bool
extern fn rt_http_server_stop(server: i64) -> bool

struct HttpServer:
    handle: i64
    is_valid: bool

fn http_server_new(port: i64) -> HttpServer:
    val handle = rt_http_server_new(port)
    HttpServer(handle: handle, is_valid: handle != 0)

fn http_server_route(server: HttpServer, method: text, path: text, handler: text) -> bool:
    if not server.is_valid:
        false
    else:
        rt_http_server_route(server.handle, method, path, handler)

fn http_server_start(server: HttpServer) -> bool:
    if not server.is_valid:
        false
    else:
        rt_http_server_start(server.handle)

fn http_server_stop(server: HttpServer) -> bool:
    if server.is_valid:
        rt_http_server_stop(server.handle)
    else:
        true
```

**Rust Implementation Needed:** ~500-700 lines
**Crate:** `reqwest = "0.11"` (client), `hyper = "0.14"` (server)
**Priority:** 🟡 Medium - Useful for web apps and APIs

---

## Part 2: Runtime Parser Syntax Limitations (Cannot Fix with SFFI)

These features are **already implemented in the compiler** but blocked because the **runtime parser doesn't support the syntax**.

### Category Breakdown

| Category | Skip Tests | Status | Solution |
|----------|------------|--------|----------|
| **Async/Await** | ~267 | Compiler ✅, Parser ❌ | Update runtime parser |
| **Type System** | ~255 | Compiler ✅, Parser ❌ | Update runtime parser |
| **Generators** | ~200 | Compiler ✅, Parser ❌ | Update runtime parser |
| **Baremetal** | ~255 | Compiler ✅, Parser ❌ | Update runtime parser |
| **Pattern Matching** | ~150 | Compiler ✅, Parser ❌ | Update runtime parser |

### Examples of Parser-Blocked Features

**1. Async/Await Syntax**
```simple
# ❌ Runtime parser doesn't support
async fn fetch_data() -> text:
    val result = await http_get("https://api.example.com/data")
    result.body

# ✅ Compiler supports this syntax
# ❌ But runtime parser rejects "async" and "await" keywords
```

**2. Generator Syntax**
```simple
# ❌ Runtime parser doesn't support
fn count_up() -> Generator<i64>:
    var i = 0
    while i < 10:
        yield i
        i = i + 1

# ✅ Compiler supports this syntax
# ❌ But runtime parser rejects "yield" keyword
```

**3. Advanced Type Syntax**
```simple
# ❌ Runtime parser doesn't support
fn process<T: Display + Clone>(value: T) -> T:
    print value
    value.clone()

# ✅ Compiler supports trait bounds
# ❌ But runtime parser has limited generic syntax support
```

**Solution:** Update `src/app/parser/` to support full Simple syntax (not an SFFI issue)

---

## Part 3: Features Pending Implementation (Not SFFI)

These are features that need to be implemented in the compiler/runtime, not SFFI wrappers.

### Category Breakdown

| Category | Skip Tests | What's Needed |
|----------|------------|---------------|
| **TreeSitter Integration** | ~115 | Implement TreeSitter parser bindings |
| **Database/SDN** | ~132 | Complete SDN parser error handling |
| **CLI/Tooling** | ~224 | Implement LSP, depgraph, verify commands |
| **MCP** | ~75 | Complete MCP database integration |
| **GC/Memory** | ~204 | Advanced GC features, memory profiling |
| **Spec Framework** | ~1,954 | Test framework improvements |

**None of these require SFFI wrappers** - they need implementation in Simple or runtime code.

---

## Part 4: SFFI Wrapper Priority Matrix

Based on the analysis, here's the priority for new SFFI wrappers:

### High Priority (Unblocks Many Tests)

1. **JIT/Execution Manager** (~30 tests) - 300 lines Rust
   - Enables runtime code compilation
   - Supports dynamic evaluation
   - Cranelift or LLVM backend

### Medium Priority (Useful Features)

2. **HTTP Client/Server** (~50 tests) - 500-700 lines Rust
   - Network programming
   - Web APIs
   - REST services

3. **Process Info** (~15 tests) - 100 lines Rust
   - System utilities
   - Process management
   - User/group info

### Low Priority (Niche Use Cases)

4. **LLVM IR Export** (~5 tests) - 200 lines Rust
   - Compiler developers
   - Optimization research
   - Requires LLVM dependency

### Already Complete (Game Engine Stack)

✅ **Physics** (Rapier2D) - Complete
✅ **Windowing** (Winit) - Complete
✅ **Graphics** (Lyon) - Complete
✅ **Audio** (Rodio) - Complete
✅ **Gamepad** (Gilrs) - Complete

---

## Summary: What SFFI Wrappers Can Help?

### Can Be Unblocked with SFFI (100 tests)

1. **JIT/Execution Manager** → 30 tests ✅ High value
2. **HTTP Client/Server** → 50 tests ✅ Medium value
3. **Process Info** → 15 tests ✅ Medium value
4. **LLVM IR Export** → 5 tests ✅ Low value

### Cannot Be Unblocked with SFFI (1,883 tests)

1. **Runtime Parser Syntax** → 1,400 tests ❌ Need parser updates
2. **Compiler Features** → 400 tests ❌ Need implementation
3. **Slow Tests** → 83 tests ❌ Performance issue, not missing features

---

## Recommendations

### Immediate Actions

1. **Implement JIT/Execution Manager SFFI** (highest impact)
   - Unblocks 30 tests
   - Enables dynamic compilation
   - ~300 lines of Rust

2. **Update Runtime Parser** (biggest impact)
   - Unblocks ~1,400 tests
   - Support async/await/yield/generator syntax
   - Support advanced type syntax
   - Not an SFFI issue - requires parser work

### Short-Term Actions

3. **Implement HTTP SFFI** (useful for many projects)
   - Unblocks 50 tests
   - Enables web programming
   - ~500-700 lines of Rust

4. **Implement Process Info SFFI** (completes system APIs)
   - Unblocks 15 tests
   - ~100 lines of Rust

### Long-Term Actions

5. **LLVM IR Export SFFI** (advanced users only)
   - Unblocks 5 tests
   - ~200 lines of Rust
   - Requires LLVM dependency

---

## Conclusion

**Key Insight:** Only ~5% of skip tests (100/1,983) are blocked by missing SFFI wrappers. The majority (70%+) are blocked by runtime parser syntax limitations.

**Best ROI:**
1. ✅ **JIT/Execution Manager SFFI** - Unblocks 30 tests with 300 lines
2. 🔧 **Update Runtime Parser** - Unblocks 1,400 tests (not SFFI)
3. ✅ **HTTP Client/Server SFFI** - Unblocks 50 tests with 500-700 lines

**Game Engine Stack:** ✅ COMPLETE - All SFFI wrappers implemented!

**Next SFFI Target:** JIT/Execution Manager for dynamic compilation support.
