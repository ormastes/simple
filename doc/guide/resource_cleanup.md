# Resource Cleanup Framework Guide

**Version:** 1.0
**Last Updated:** 2026-01-25

This guide covers Simple's unified resource cleanup framework, which provides consistent patterns for managing system resources like files, network sockets, and threads.

---

## Table of Contents

- [Introduction](#introduction)
- [The Resource Trait](#the-resource-trait)
- [Using defer for Cleanup](#using-defer-for-cleanup)
- [Using the with Statement](#using-the-with-statement)
- [Automatic Leak Detection](#automatic-leak-detection)
- [The LeakTracked Mixin](#the-leaktracked-mixin)
- [Best Practices](#best-practices)
- [Migration Guide](#migration-guide)

---

## Introduction

Resource management is critical for writing correct and efficient programs. System resources like file handles, network sockets, and memory mappings are limited and must be properly released when no longer needed. Failing to do so causes:

- **Resource leaks** - Gradual exhaustion of available handles
- **Memory leaks** - Memory that can never be reclaimed
- **Data corruption** - Files not properly flushed or closed
- **Network issues** - Connections left in invalid states

Simple provides a unified framework for resource cleanup through:

1. **Resource trait** - Common interface for closeable resources
2. **defer statement** - Scope-based cleanup
3. **with statement** - Automatic cleanup with context managers
4. **ResourceRegistry** - Runtime leak tracking
5. **LeakTracked mixin** - Automatic resource registration

---

## The Resource Trait

The `Resource` trait defines a unified interface for resources that require explicit cleanup:

```simple
trait Resource:
    fn close()              # Close and release the resource
    fn is_open() -> bool    # Check if resource is still open
    fn resource_name() -> text  # Human-readable name for errors
```

For async resources (like network sockets), use `AsyncResource`:

```simple
trait AsyncResource:
    async fn close()        # Async close for resources needing async cleanup
    fn is_open() -> bool
    fn resource_name() -> text
```

### Resources Implementing These Traits

| Resource | Trait | Location |
|----------|-------|----------|
| `File` | `AsyncResource` | `host.async_nogc_mut.io.fs.file` |
| `TcpStream` | `AsyncResource` | `host.common.net.tcp` |
| `TcpListener` | `AsyncResource` | `host.common.net.tcp` |
| `UdpSocket` | `AsyncResource` | `host.common.net.udp` |
| `ThreadHandle` | `Resource` | `concurrency.threads` |
| `LimitedThreadHandle` | `Resource` | `concurrency.threads` |
| `Channel` | `Resource` | `concurrency.channels` |
| `BoundedChannel<T>` | `Resource` | `concurrency.channels` |
| `UnboundedChannel<T>` | `Resource` | `concurrency.channels` |
| `MmapRegion` | `Resource` | `file.mmap` |

### Implementing Resource for Custom Types

```simple
use core.resource.Resource

struct MyResource:
    handle: i64
    path: text

impl Resource for MyResource:
    fn close():
        if self.handle != -1:
            native_close(self.handle)
            self.handle = -1

    fn is_open() -> bool:
        self.handle != -1

    fn resource_name() -> text:
        "MyResource({self.path})"
```

---

## Using defer for Cleanup

The `defer` statement schedules cleanup to run when the current scope exits, regardless of how it exits (normal completion, early return, or exception).

### Basic Usage

```simple
fn process_file(path: text) -> Result<text, IoError>:
    val file = await File.open(path, OpenMode::Read)?
    defer file.close()  # Runs when function exits

    val content = await file.read_all()?
    return Ok(content)
    # file.close() called automatically here
```

### Multiple Defers (LIFO Order)

Defers execute in Last-In-First-Out order:

```simple
fn multi_resource():
    val a = acquire_resource_a()
    defer release_a(a)  # Released third

    val b = acquire_resource_b()
    defer release_b(b)  # Released second

    val c = acquire_resource_c()
    defer release_c(c)  # Released first

    use_resources(a, b, c)
# Order: release_c, release_b, release_a
```

### Defer Runs on Early Return

```simple
fn conditional_process(path: text) -> Result<(), IoError>:
    val file = await File.open(path, OpenMode::Read)?
    defer file.close()

    val header = await file.read(4)?
    if header != MAGIC_BYTES:
        return Err(IoError::InvalidFormat)  # close() still called!

    # ... process file ...
    return Ok(())
```

### Defer Runs on Exception

```simple
fn risky_operation():
    val conn = Database.connect(url)?
    defer conn.close()

    # Even if this throws, conn.close() is called
    conn.execute("DANGEROUS QUERY")
```

---

## Using the with Statement

The `with` statement provides automatic cleanup through context managers:

### Basic with Statement

```simple
# File is automatically closed when block exits
with File.open("data.txt") as file:
    val content = file.read()
    process(content)
# file.close() called automatically
```

### Async with Statement

For async resources, use `async with`:

```simple
async with await TcpStream.connect_str("127.0.0.1:8080") as stream:
    await stream.write_all(request)?
    val response = await stream.read()?
# stream.close() called automatically
```

### Multiple Resources

```simple
with File.open("input.txt") as input, File.create("output.txt") as output:
    val data = input.read()
    output.write(process(data))
# Both files closed automatically
```

### Context Manager Protocol

Resources implementing `__exit__` or `__aexit__` are context managers:

```simple
impl ContextManager for MyResource:
    fn __enter__(self) -> MyResource:
        return self

    fn __exit__(self, exc: Option<Exception>) -> bool:
        self.close()
        return false  # Don't suppress exceptions
```

---

## Automatic Leak Detection

The `ResourceRegistry` tracks open resources and can detect leaks at runtime.

### Checking for Leaks

```simple
use core.resource_registry.ResourceRegistry

# At end of test or application
val leaks = ResourceRegistry.check_leaks()
if leaks.len() > 0:
    print "WARNING: Resource leaks detected!"
    print ResourceRegistry.leak_report()
```

### ResourceRegistry API

```simple
struct ResourceRegistry:
    # Register a resource for tracking
    static fn register(resource_name: text, location: text) -> i64

    # Unregister when closed
    static fn unregister(id: i64)

    # Get all open resources
    static fn get_open_resources() -> List<ResourceEntry>

    # Check for leaks
    static fn check_leaks() -> List<ResourceEntry>

    # Get human-readable report
    static fn leak_report() -> text

    # Clear registry (for testing)
    static fn clear()
```

### Example Leak Report

```
Resource Leaks Detected (2):
  - File(test.txt) created at File.open("test.txt")
  - TcpStream(127.0.0.1:8080) created at TcpStream.connect("127.0.0.1:8080")
```

---

## The LeakTracked Mixin

The `LeakTracked` mixin provides automatic resource tracking with minimal boilerplate.

### Using LeakTracked

```simple
use core.leak_tracked.LeakTracked

struct MyResource with LeakTracked:
    handle: i64
    path: text

impl MyResource:
    static fn open(path: text) -> MyResource:
        val handle = native_open(path)
        var r = MyResource(handle: handle, path: path)
        # Start tracking
        r._start_tracking("MyResource.open(\"{path}\")")
        return r

    fn close():
        # Stop tracking
        self._stop_tracking()
        native_close(self.handle)
```

### LeakTracked Methods

```simple
mixin LeakTracked:
    # Start tracking this resource
    me _start_tracking(location: text)

    # Stop tracking (call on close)
    me _stop_tracking()

    # Check if being tracked
    fn is_tracked() -> bool

    # Get tracking ID
    fn tracking_id() -> Option<i64>
```

### How It Works

1. When `_start_tracking` is called, the resource is registered with `ResourceRegistry`
2. The location string helps identify where the resource was created
3. When `_stop_tracking` is called, the resource is unregistered
4. If a resource is never closed, it appears in leak reports

---

## Best Practices

### 1. Always Use defer or with for Resources

```simple
# Good - always cleaned up
fn good_example():
    val file = File.open(path)?
    defer file.close()
    # ...

# Bad - may leak on error
fn bad_example():
    val file = File.open(path)?
    # ... might throw ...
    file.close()  # May never run!
```

### 2. Close Resources Early When Possible

```simple
fn process_data():
    val data = with File.open("data.txt") as f:
        f.read()  # File closed immediately after read

    # Process data without holding file open
    expensive_computation(data)
```

### 3. Use LeakTracked for Custom Resources

```simple
struct MyConnection with LeakTracked:
    # ... fields ...

impl MyConnection:
    static fn connect(url: text) -> MyConnection:
        var conn = MyConnection(...)
        conn._start_tracking("MyConnection.connect(\"{url}\")")
        return conn

    fn close():
        self._stop_tracking()
        # ... cleanup ...
```

### 4. Check for Leaks in Tests

```simple
describe "File Operations":
    # Clear registry before each test
    before_each:
        ResourceRegistry.clear()

    # Check for leaks after each test
    after_each:
        val leaks = ResourceRegistry.check_leaks()
        assert leaks.len() == 0, ResourceRegistry.leak_report()

    it "reads file content":
        with File.open("test.txt") as f:
            assert f.read() == "expected"
```

### 5. Prefer with Over Manual defer

```simple
# Preferred - clearer intent
with File.open(path) as file:
    process(file)

# Also fine - more flexible
val file = File.open(path)?
defer file.close()
# ... complex logic that needs the file ...
```

---

## Migration Guide

### From Manual Close Calls

Before:
```simple
fn old_style():
    val file = File.open(path)?
    val content = file.read()
    file.close()
    return content
```

After:
```simple
fn new_style():
    with File.open(path) as file:
        return file.read()
```

### Adding LeakTracked to Existing Resources

1. Add the mixin to the struct:
   ```simple
   struct MyResource with LeakTracked:
       # existing fields...
   ```

2. Add tracking in creation method:
   ```simple
   static fn create() -> MyResource:
       var r = MyResource(...)
       r._start_tracking("MyResource.create()")
       return r
   ```

3. Add stop tracking in close:
   ```simple
   fn close():
       self._stop_tracking()
       # existing cleanup...
   ```

### Implementing Resource for Existing Types

```simple
# Add to existing impl block or create new one
impl Resource for MyExistingType:
    fn close():
        # Use existing cleanup method
        self.existing_cleanup()

    fn is_open() -> bool:
        self.handle != INVALID

    fn resource_name() -> text:
        "MyExistingType"
```

---

## See Also

- [Syntax Quick Reference](syntax_quick_reference.md) - Resource cleanup syntax
- [core.resource](../../src/lib/std/src/core/resource.spl) - Resource trait source
- [core.resource_registry](../../src/lib/std/src/core/resource_registry.spl) - Registry source
- [core.leak_tracked](../../src/lib/std/src/core/leak_tracked.spl) - LeakTracked mixin source
