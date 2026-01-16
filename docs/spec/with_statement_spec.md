# With Statement (Context Managers)

*Source: `simple/std_lib/test/features/control_flow/with_statement_spec.spl`*

---

# With Statement (Context Managers)

**Feature ID:** #51
**Category:** Control Flow
**Difficulty:** 2/5 (Beginner-Intermediate)
**Status:** Complete

## Overview

The `with` statement provides RAII (Resource Acquisition Is Initialization) pattern support for safe
resource management. It ensures that cleanup code (`__exit__`) is always called, even if exceptions
occur in the body, preventing resource leaks.

**Design Philosophy:**
Simple follows Python's context manager protocol, enabling automatic resource cleanup for files,
locks, database connections, and other resources that require deterministic cleanup.

## Syntax

### Basic With Statement

```simple
with resource:
    # Use resource
    # __exit__ called automatically when block ends
```

### With Alias Binding

```simple
with open("file.txt", "r") as file:
    val content = file.read()
    # file.__exit__() called automatically
```

**Grammar:**
```
with_stmt = 'with' expression ('as' identifier)? ':' NEWLINE INDENT statement+ DEDENT
```

## Protocol

Context managers must implement two methods:

- `__enter__()` - Called before body, return value bound to alias
- `__exit__()` - Called after body (always, even on exception)

```simple
class FileHandle:
    handle: i32
    closed: bool

impl FileHandle:
    fn __enter__() -> FileHandle:
        # Open the file
        return self

    fn __exit__():
        # Close the file
        self.close()
```

## Runtime Representation

**Execution Flow:**
1. Evaluate resource expression
2. Call `__enter__()` on resource
3. If `as name` provided, bind result of `__enter__()` to name
4. Execute body block
5. **Always** call `__exit__()` on resource (even if exception occurred)
6. Remove name binding (if created)

**Error Handling:**
The `__exit__` method is called even if the body raises an exception, ensuring cleanup
always happens. This is critical for preventing resource leaks.

## Comparison with Other Languages

| Feature | Simple | Python | Ruby | JavaScript | Rust | Go |
|---------|--------|--------|------|------------|------|-----|
| Context managers | `with` | `with` | Block form | try-finally | RAII | `defer` |
| Auto-cleanup | ✅ Yes | ✅ Yes | ✅ Yes | ❌ Manual | ✅ Yes | ✅ Yes |
| Enter/exit protocol | ✅ Yes | ✅ Yes | ❌ No | ❌ No | ❌ No | ❌ No |
| Exception safety | ✅ Yes | ✅ Yes | ✅ Yes | ✅ Yes | ✅ Yes | ✅ Yes |

## Common Patterns

### File Handling

```simple
with open("data.txt", "r") as file:
    val content = file.read()
    process(content)
# file automatically closed here
```

### Lock Management

```simple
with mutex.lock() as guard:
    # Critical section
    shared_data.update()
# Lock automatically released
```

### Database Transactions

```simple
with db.transaction() as tx:
    tx.execute("INSERT INTO users VALUES (?)", name)
    tx.execute("UPDATE stats SET count = count + 1")
# Auto-commit on success, rollback on exception
```

### Multiple Resources (Nested)

```simple
with open("input.txt", "r") as input:
    with open("output.txt", "w") as output:
        for line in input.lines():
            output.write(transform(line))
```

## Implementation Files

**Parser:** `src/parser/src/stmt_parsing/control_flow.rs:165-223` - With statement parsing
**AST:** `src/parser/src/ast/nodes/statements.rs:138-147` - WithStmt struct
**Interpreter:** `src/compiler/src/interpreter_control.rs:347-409` - exec_with()
**Tests:** `src/driver/tests/interpreter_control.rs` - With statement tests

## Related Features

- **Error Handling (#18):** Exception safety with with statements
- **Classes (#30):** Implementing __enter__/__exit__ methods
- **File I/O (#55):** File handles with automatic cleanup
- **Concurrency (#40):** Lock guards and mutex management

## Limitations and Future Work

**Current Limitations:**
- No `__exit__` exception argument (Python passes exception info)
- No multiple resources in single `with` statement

**Planned Features:**
- Multiple resources: `with open(a) as x, open(b) as y:`
- Exception info in `__exit__(exc_type, exc_val, exc_tb)`
- Async with: `async with` for async context managers

## With Statement - RAII Pattern for Resource Management

    The with statement provides automatic resource cleanup through the context manager
    protocol. It guarantees that `__exit__` is called when leaving the block, regardless
    of how the block is exited (normal completion, return, or exception).

    **Key Properties:**
    - Resources are acquired at block entry via `__enter__`
    - Cleanup happens automatically via `__exit__`
    - Exception-safe: `__exit__` called even on errors
    - Optional alias binding with `as name`

    **Implementation:** `src/compiler/src/interpreter_control.rs:exec_with()`

**Given** a class with __enter__ method
        **When** using it in a with statement
        **Then** __enter__ is called before the body executes

        The __enter__ method is called immediately when entering the with block,
        allowing resource initialization.

**Given** a class with __exit__ method
        **When** the with block completes
        **Then** __exit__ is called automatically

        The __exit__ method is always called when leaving the with block,
        ensuring cleanup happens regardless of how the block is exited.

**Given** a class where __enter__ returns a value
        **When** using `with resource as name:`
        **Then** the name is bound to the return value of __enter__

        This allows returning a different object than the context manager itself,
        useful for database connections that return a cursor.

## Exception Safety with Context Managers

    The with statement guarantees that __exit__ is called even when exceptions
    occur in the body, making it safe for managing resources that must be cleaned up.

    **Key Properties:**
    - __exit__ called on normal completion
    - __exit__ called on exception
    - __exit__ called on early return
    - Resources never leaked

    **Implementation:** Uses try-finally semantics internally

**Given** a with block that encounters an error
        **When** an exception is raised in the body
        **Then** __exit__ is still called for cleanup

        This is the critical safety property of context managers - cleanup
        always happens regardless of errors.

## Real-World Context Manager Patterns

    Context managers are most useful for managing resources that require
    deterministic cleanup, such as files, locks, and database connections.

**Given** a counter that tracks active resources
        **When** using with to manage the count
        **Then** the counter is properly incremented and decremented

        This pattern is useful for tracking active connections, threads, etc.
