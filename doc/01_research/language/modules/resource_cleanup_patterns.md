# Resource Cleanup Patterns Research

**Date:** 2026-01-25
**Status:** Research Complete
**Purpose:** Prevent resource leaks in tests, establish cleanup framework patterns

---

## Executive Summary

Resource leaks in tests are a common problem, especially with:
- File handles left open
- Network sockets not closed
- Cached values accumulating across tests
- Thread-local state pollution

This document analyzes the current Simple language cleanup implementation, compares with industry best practices, and proposes improvements.

---

## Current State in Simple

### Existing Cleanup Infrastructure

The test runner (`simple_test.rs:258-278`) implements comprehensive cleanup:

```rust
// Before each test file:
clear_interpreter_state();        // BDD registries, module globals, DI singletons
clear_bdd_state();               // Indentation, counts, hooks, lazy values
clear_module_cache();            // Prevent memory accumulation
clear_class_instantiation_state(); // Clear IN_NEW_METHOD tracking
clear_macro_state();             // Clear macro contract cache
clear_effects_state();           // Clear effect tracking
clear_io_state();                // Close file handles
clear_net_state();               // Close socket handles
clear_i18n_state();              // Clear locale strings cache
clear_all_runtime_registries();  // HP collections, regex cache, etc.
```

### Common Leak Patterns Found

| Pattern | Location | Impact |
|---------|----------|--------|
| **Accumulated Registries** | Thread-local HashMap/Vec | Memory growth per test |
| **File Handle Pool** | `FILE_HANDLES` in io.rs | File descriptor exhaustion |
| **Socket Pool** | `SOCKET_REGISTRY` in net.rs | Port exhaustion |
| **Cached Values** | Regex, modules | Memory accumulation |
| **BDD Test State** | 10+ thread-local fields | State pollution |
| **Macro State** | Expansion tracking | Incorrect nested macro behavior |

### Current Strengths

1. **Centralized cleanup** - Single point of cleanup before each test
2. **Thread-local isolation** - State stored in `thread_local!` with `RefCell`
3. **Explicit Drop documentation** - Comments note that `.clear()` triggers Drop
4. **Layered architecture** - Cleanup organized by subsystem

### Current Gaps

1. No `defer`-like construct in Simple language itself
2. No automatic cleanup for user-created resources in tests
3. No fixture lifecycle management (`before_each`/`after_each` exist but resource tracking is manual)
4. Missing cleanup for: `reset_execution_count()`, `INTERRUPT_REQUESTED`, `DEBUG_MODE`

---

## Industry Patterns Comparison

### Pattern 1: RAII / Drop (Rust, C++)

**Concept:** Tie resource lifetime to object lifetime.

```rust
impl Drop for DatabaseConnection {
    fn drop(&mut self) {
        self.handle.close();
    }
}
```

**Simple Language Status:**
- Partial - RuntimeValue has Drop for some types
- Gap - No user-defined Drop equivalent yet

**Recommendation:** Add `fn drop(self)` method support to Simple classes.

### Pattern 2: Context Managers (Python with)

**Concept:** Explicit scope-based cleanup with `__enter__`/`__exit__`.

```python
with open("file.txt") as f:
    data = f.read()
# File closed automatically
```

**Simple Language Equivalent Proposal:**

```simple
# Option A: using statement
using file = File.open("test.txt"):
    file.write("data")
# file.close() called automatically

# Option B: Resource trait
trait Resource:
    fn close(self)

impl Resource for File:
    fn close(self):
        self.handle.close()
```

### Pattern 3: defer (Go, Zig)

**Concept:** Schedule cleanup to run at scope exit.

```go
file := openFile()
defer file.Close()
// ... use file
```

**Simple Language Equivalent Proposal:**

```simple
fn process_data():
    val file = File.open("data.txt")
    defer file.close()  # Runs at function exit

    val db = Database.connect()
    defer db.disconnect()

    # Business logic...
    # Both cleanup calls run in LIFO order
```

### Pattern 4: errdefer (Zig)

**Concept:** Cleanup only on error path.

```zig
const resource = try allocate();
errdefer free(resource);  // Only if error propagates
try resource.setup();
return resource;  // Success - no cleanup
```

**Simple Language Equivalent Proposal:**

```simple
fn initialize() -> Result<Resource, Error>:
    val resource = allocate()?
    errdefer resource.free()  # Only if we return Err

    resource.setup()?
    Ok(resource)  # Success - no errdefer cleanup
```

### Pattern 5: Test Fixtures with Lifecycle (JUnit, pytest, RSpec)

**Concept:** Framework-managed setup/teardown hooks.

**pytest yield fixture:**
```python
@pytest.fixture
def database():
    db = create_db()
    yield db
    db.cleanup()  # Teardown
```

**RSpec around hook:**
```ruby
around(:each) do |example|
    DB.transaction(rollback: :always) { example.run }
end
```

**Simple Language Current State:**

```simple
describe "Database tests":
    before_each:
        @db = Database.connect()

    after_each:
        @db.disconnect()  # Manual cleanup required

    it "queries data":
        @db.query("SELECT 1")
```

**Proposed Enhancement - Resource Fixtures:**

```simple
describe "Database tests":
    # Auto-cleanup fixture
    fixture db = Database.connect()

    it "queries data":
        db.query("SELECT 1")
    # db automatically closed after each test
```

### Pattern 6: t.Cleanup() (Go)

**Concept:** Register cleanup functions that run after test completes, including subtests.

```go
func setupDB(t *testing.T) *DB {
    db := connect()
    t.Cleanup(func() { db.Close() })
    return db
}
```

**Simple Language Equivalent Proposal:**

```simple
fn setup_db(test: TestContext) -> Database:
    val db = Database.connect()
    test.cleanup(\: db.close())
    db
```

---

## Resource Trait with Leak Detection

### Core Design: The `Resource` Trait

All resources must implement the `Resource` trait. This enables:
1. **Unified cleanup interface** - All resources use `.close()`
2. **Leak detection** - Track unclosed resources
3. **Automatic cleanup** - `defer`/`using` work with any Resource
4. **Static analysis** - Lint can check Resource types are properly managed

### Trait Definition

```simple
# Core resource trait - ALL resources must implement this
trait Resource:
    # Called to release the resource
    fn close(me self)

    # Optional: Check if already closed (default: false)
    fn is_closed(self) -> bool:
        false

    # Optional: Resource name for debugging/leak reports
    fn resource_name(self) -> text:
        "Resource"
```

### Mixin for Leak Tracking

```simple
# Mixin that adds leak detection to any Resource
mixin LeakTracked:
    # Class-level tracking (static)
    static var _allocated: Set<i64> = {}
    static var _allocation_sites: Dict<i64, text> = {}

    # Instance tracking
    var _resource_id: i64 = 0
    var _closed: bool = false

    # Called when resource is created
    me on_allocate():
        self._resource_id = generate_unique_id()
        self._closed = false
        Self._allocated.add(self._resource_id)
        Self._allocation_sites[self._resource_id] = get_stack_trace()

    # Called when resource is closed
    me on_close():
        if not self._closed:
            self._closed = true
            Self._allocated.remove(self._resource_id)
            Self._allocation_sites.remove(self._resource_id)

    fn is_closed(self) -> bool:
        self._closed

    # Check for leaks (call at end of test/scope)
    static fn check_leaks() -> List<text>:
        val leaks = []
        for id in Self._allocated:
            val site = Self._allocation_sites.get(id) ?? "unknown"
            leaks.push("Leaked {Self.resource_name()} allocated at: {site}")
        leaks

    static fn leak_count() -> i32:
        Self._allocated.len()

    static fn clear_tracking():
        Self._allocated.clear()
        Self._allocation_sites.clear()
```

### Standard Resource Implementations

```simple
# File implements Resource with leak tracking
class File with LeakTracked:
    var handle: FileHandle
    var path: text

    static fn open(path: text, mode: text = "r") -> Result<File, IOError>:
        val handle = native_open(path, mode)?
        val file = File(handle: handle, path: path)
        file.on_allocate()  # Track allocation
        Ok(file)

    me close():
        if not self.is_closed():
            native_close(self.handle)
            self.on_close()  # Track closure

    fn resource_name(self) -> text:
        "File({self.path})"

impl Resource for File


# Socket implements Resource with leak tracking
class Socket with LeakTracked:
    var handle: SocketHandle
    var address: text

    static fn connect(addr: text, port: i32) -> Result<Socket, NetError>:
        val handle = native_connect(addr, port)?
        val socket = Socket(handle: handle, address: "{addr}:{port}")
        socket.on_allocate()
        Ok(socket)

    me close():
        if not self.is_closed():
            native_close_socket(self.handle)
            self.on_close()

    fn resource_name(self) -> text:
        "Socket({self.address})"

impl Resource for Socket


# Database connection
class DbConnection with LeakTracked:
    var conn: NativeConnection
    var url: text

    static fn connect(url: text) -> Result<DbConnection, DbError>:
        val conn = native_db_connect(url)?
        val db = DbConnection(conn: conn, url: url)
        db.on_allocate()
        Ok(db)

    me close():
        if not self.is_closed():
            native_db_close(self.conn)
            self.on_close()

    fn resource_name(self) -> text:
        "DbConnection({self.url})"

impl Resource for DbConnection
```

### Global Resource Registry

```simple
# Central registry for ALL resource types
module ResourceRegistry:
    var trackers: List<fn() -> i32> = []
    var checkers: List<fn() -> List<text>> = []
    var clearers: List<fn()> = []

    # Register a resource type for tracking
    fn register<T: Resource + LeakTracked>():
        trackers.push(\: T.leak_count())
        checkers.push(\: T.check_leaks())
        clearers.push(\: T.clear_tracking())

    # Check all registered resource types for leaks
    fn check_all_leaks() -> List<text>:
        val all_leaks = []
        for checker in checkers:
            all_leaks.extend(checker())
        all_leaks

    # Total leak count across all types
    fn total_leak_count() -> i32:
        trackers.map(\f: f()).sum()

    # Clear all tracking (call before each test)
    fn clear_all():
        for clearer in clearers:
            clearer()

    # Assert no leaks (for tests)
    fn assert_no_leaks():
        val leaks = check_all_leaks()
        if leaks.?:
            val msg = leaks.join("\n")
            panic("Resource leaks detected:\n{msg}")

# Register standard types at module load
ResourceRegistry.register<File>()
ResourceRegistry.register<Socket>()
ResourceRegistry.register<DbConnection>()
```

### Integration with Test Framework

```simple
# BDD framework integration
describe "File operations":
    # Automatic leak check after each test
    after_each:
        ResourceRegistry.assert_no_leaks()

    before_each:
        ResourceRegistry.clear_all()

    it "reads file without leak":
        val file = File.open("test.txt")?
        val data = file.read_all()
        file.close()  # Properly closed - no leak

    it "FAILS - leaks file handle":
        val file = File.open("test.txt")?
        val data = file.read_all()
        # Forgot to close! Test will fail with leak report
```

### Automatic Leak Check Mode

```simple
# Enable automatic leak checking for all tests
@leak_check  # Decorator enables leak checking for this describe block
describe "Integration tests":
    it "uses multiple resources":
        using val file = File.open("config.txt"):
            using val db = DbConnection.connect("postgres://localhost"):
                val config = file.read_all()
                db.execute(config)
        # Both automatically closed via `using`
        # Leak check runs automatically after test
```

### Leak Report Format

When leaks are detected, the report shows:

```
=== RESOURCE LEAK REPORT ===
Test: "reads and processes data" (file_spec.spl:42)

Leaked resources (3):
  1. File(data.txt)
     Allocated at: file_spec.spl:45 in process_data()
     Stack: process_data() -> read_config() -> File.open()

  2. Socket(localhost:8080)
     Allocated at: file_spec.spl:52 in connect_service()

  3. DbConnection(postgres://localhost/test)
     Allocated at: file_spec.spl:58 in setup_db()

Suggestion: Use `defer resource.close()` or `using val r = ...:`
```

### Compile-Time Enforcement (Lint)

```simple
# Lint rule: resource_must_close
# Triggers when Resource type assigned but never closed

fn process():
    val file = File.open("data.txt")?  # WARNING: Resource not closed
    val data = file.read_all()
    # Missing: file.close() or defer or using

# Lint output:
# warning[resource_must_close]: Resource 'file' of type File is never closed
#   --> process.spl:2:9
#   |
# 2 |     val file = File.open("data.txt")?
#   |         ^^^^ Resource created here
#   |
#   = help: add `defer file.close()` after this line
#   = help: or use `using val file = File.open("data.txt")?:`
```

### Resource Trait Hierarchy

```
trait Resource
    │
    ├── fn close(me self)           # Required
    ├── fn is_closed(self) -> bool  # Optional (default: false)
    └── fn resource_name(self)      # Optional (default: "Resource")

mixin LeakTracked
    │
    ├── static var _allocated       # Track live instances
    ├── static var _allocation_sites # Track where allocated
    │
    ├── me on_allocate()            # Call in constructor
    ├── me on_close()               # Call in close()
    │
    ├── static fn check_leaks()     # Get leak report
    ├── static fn leak_count()      # Count leaks
    └── static fn clear_tracking()  # Reset for next test

Implementors:
    File with LeakTracked implements Resource
    Socket with LeakTracked implements Resource
    DbConnection with LeakTracked implements Resource
    TempFile with LeakTracked implements Resource
    Lock with LeakTracked implements Resource
    Transaction with LeakTracked implements Resource
```

### Debug Mode: Verbose Tracking

```simple
# Enable verbose resource tracking (for debugging)
ResourceRegistry.set_verbose(true)

# Output during execution:
# [RESOURCE] File.open("config.txt") -> id=1 at main.spl:10
# [RESOURCE] Socket.connect("localhost", 8080) -> id=2 at main.spl:15
# [RESOURCE] File.close(id=1) at main.spl:25
# [RESOURCE] Socket.close(id=2) at main.spl:30
# [RESOURCE] All resources closed. No leaks.
```

---

## Recommended Framework for Simple

### Tier 0: Resource Trait Foundation (NEW - Highest Priority)

#### 0.1 Define `Resource` Trait

```simple
trait Resource:
    fn close(me self)
    fn is_closed(self) -> bool
    fn resource_name(self) -> text
```

**Implementation:** Add to `src/lib/std/src/compiler_core/resource.spl`

#### 0.2 Add `LeakTracked` Mixin

```simple
mixin LeakTracked:
    # ... as defined above
```

**Implementation:** Add to `src/lib/std/src/compiler_core/resource.spl`

#### 0.3 Update All Resource Types

- `File` implements `Resource` with `LeakTracked`
- `Socket` implements `Resource` with `LeakTracked`
- `DbConnection` implements `Resource` with `LeakTracked`
- `TempFile` implements `Resource` with `LeakTracked`
- `Lock`/`Mutex` implements `Resource` with `LeakTracked`

### Tier 1: Language-Level (High Impact)

#### 1.1 Add `defer` Statement

```simple
fn process():
    val file = File.open("data.txt")
    defer file.close()

    val conn = Connection.new()
    defer conn.disconnect()

    # Multiple defers run in LIFO order
    process_data(file, conn)
```

**Implementation:** Compile to try-finally equivalent in MIR.

#### 1.2 Add `errdefer` Statement

```simple
fn create_resource() -> Result<Resource, Error>:
    val r = allocate()?
    errdefer r.free()

    r.initialize()?  # If this fails, r.free() runs
    Ok(r)
```

**Implementation:** Track error propagation path, insert cleanup on error branches.

### Tier 2: Trait-Based (Medium Impact)

#### 2.1 Add `Closeable` Trait

```simple
trait Closeable:
    fn close(self)

# Auto-implemented for types with close method
impl Closeable for File
impl Closeable for Socket
impl Closeable for Database
```

#### 2.2 Add `using` Statement

```simple
using val file = File.open("test.txt"):
    file.write("data")
# file.close() called automatically, even on error
```

**Desugars to:**
```simple
val file = File.open("test.txt")
try:
    file.write("data")
finally:
    file.close()
```

### Tier 3: Test Framework (High Impact for Tests)

#### 3.1 Resource Fixtures

```simple
describe "Integration tests":
    # Declare resource with automatic cleanup
    resource db = Database.connect()
    resource server = TestServer.start()

    it "queries through server":
        server.register_handler(db)
        # Both cleaned up after test, in reverse order
```

**Implementation:**
- Track resource declarations in BDD context
- Call `.close()` or custom cleanup in `after_each`
- Handle cleanup errors gracefully

#### 3.2 Test Cleanup Registry

```simple
it "creates temporary files":
    val path = create_temp_file()
    test.cleanup \: File.delete(path)

    # Use file...
    # Cleanup runs after test completes
```

#### 3.3 Fixture Scopes

```simple
describe "Suite":
    # Per-suite (like @BeforeAll/@AfterAll)
    resource(scope: :suite) expensive_resource = start_server()

    # Per-test (default, like @BeforeEach/@AfterEach)
    resource db = Database.connect()
```

### Tier 4: Static Analysis (Prevention)

#### 4.1 Lint: Unclosed Resources

```
warning[resource_leak]: File opened but not closed
  --> test_io.spl:15:12
   |
15 |     val file = File.open("data.txt")
   |         ^^^^ consider using `defer file.close()` or `using`
```

#### 4.2 Lint: Missing Cleanup in Tests

```
warning[test_resource_leak]: Resource created in test without cleanup
  --> my_spec.spl:42:8
   |
42 |     val db = Database.connect()
   |         ^^ add `resource db = ...` or `test.cleanup \: db.close()`
```

---

## Implementation Priority

| Priority | Feature | Effort | Impact |
|----------|---------|--------|--------|
| **P0** | `Resource` trait | Low | Critical - foundation for all cleanup |
| **P0** | `LeakTracked` mixin | Medium | Critical - enables leak detection |
| **P0** | `defer` statement | Medium | High - prevents most leaks |
| **P0** | Update stdlib resources | Medium | High - File, Socket, etc. |
| **P1** | `ResourceRegistry` | Low | High - centralized tracking |
| **P1** | `resource` fixture keyword | Medium | High - test isolation |
| **P1** | `using` statement | Low | Medium - cleaner syntax |
| **P1** | `test.cleanup()` API | Low | Medium - flexible cleanup |
| **P2** | `errdefer` statement | Medium | Medium - error path cleanup |
| **P2** | Resource leak lint | High | High - prevention |
| **P3** | Fixture scopes | Medium | Low - performance optimization |

---

## Migration Path

### Phase 0: Resource Trait Foundation (FIRST)

1. Define `Resource` trait in `src/lib/std/src/compiler_core/resource.spl`
2. Implement `LeakTracked` mixin with allocation tracking
3. Create `ResourceRegistry` for centralized management
4. Update `File` to implement `Resource` with `LeakTracked`
5. Update `Socket` to implement `Resource` with `LeakTracked`
6. Add leak check to test runner (`after_each` equivalent)

### Phase 1: Language Constructs

1. Add `defer` to parser/compiler
2. Add `using` statement (desugars to try-finally with close)
3. Add `resource` keyword to BDD framework
4. Update existing tests to use new patterns

### Phase 2: Enhancement

1. Add `test.cleanup()` API
2. Add resource leak lint (warning level)
3. Add verbose tracking mode for debugging

### Phase 3: Advanced

1. Add `errdefer`
2. Add fixture scopes
3. Promote lint to error level for new code
4. Add IDE integration (show unclosed resources)

---

## Examples: Before and After

### Before (Current - Manual Cleanup)

```simple
describe "File operations":
    before_each:
        @file = File.open("test.txt", "w")

    after_each:
        @file.close()  # Easy to forget!

    it "writes data":
        @file.write("hello")
```

### After (With resource Keyword)

```simple
describe "File operations":
    resource file = File.open("test.txt", "w")

    it "writes data":
        file.write("hello")
    # Automatically closed after each test
```

### Before (Current - Function with Multiple Resources)

```simple
fn process_files(path1: text, path2: text) -> Result<i32, Error>:
    val input = File.open(path1)?
    val output = File.open(path2, "w")?

    # If error here, both files leak!
    val data = input.read_all()?
    output.write(transform(data))?

    input.close()
    output.close()
    Ok(data.len())
```

### After (With defer)

```simple
fn process_files(path1: text, path2: text) -> Result<i32, Error>:
    val input = File.open(path1)?
    defer input.close()

    val output = File.open(path2, "w")?
    defer output.close()

    # Even if error, both files are closed
    val data = input.read_all()?
    output.write(transform(data))?

    Ok(data.len())
```

---

## References

- [Rust RAII](https://doc.rust-lang.org/rust-by-example/scope/raii.html)
- [Go defer](https://gobyexample.com/defer)
- [Zig errdefer](https://gencmurat.com/en/posts/defer-and-errdefer-in-zig/)
- [Python Context Managers](https://realpython.com/python-with-statement/)
- [pytest Fixtures](https://docs.pytest.org/en/stable/how-to/fixtures.html)
- [Go t.Cleanup](https://www.gopherguides.com/articles/test-cleanup-in-go-1-14)
- [D Scope Guards](https://tour.dlang.org/tour/en/gems/scope-guards)

---

## Conclusion

The Simple language already has solid cleanup infrastructure at the interpreter level. The main gaps are:

1. **No standard Resource interface** - Each type handles cleanup differently
2. **No leak detection** - Unclosed resources go unnoticed
3. **No `defer` construct** - Users must manually track cleanup
4. **No automatic test resource management** - `before_each`/`after_each` require manual pairing

### Recommended Implementation Order

```
Resource trait  →  LeakTracked mixin  →  Update File/Socket  →  defer  →  using
     ↓                    ↓                     ↓                 ↓         ↓
Foundation         Tracking          Stdlib compliance      Language    Syntax sugar
```

**Key Insight:** The `Resource` trait + `LeakTracked` mixin provides the foundation that all other features build upon:

- `defer` needs to know what `.close()` means → `Resource` trait
- `using` needs automatic cleanup → `Resource` trait
- Leak detection needs to track allocations → `LeakTracked` mixin
- Lint rules need to identify resource types → `Resource` trait
- Test framework needs to check leaks → `ResourceRegistry`

**Start with Phase 0** (Resource trait) to establish the foundation, then add language features (`defer`, `using`) that leverage it.
