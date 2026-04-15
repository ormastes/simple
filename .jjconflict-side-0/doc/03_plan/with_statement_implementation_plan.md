# `with` Statement Implementation Plan

**Feature:** Context Manager with `with` statement
**Priority:** HIGH
**Impact:** 531 skipped tests (20% of test suite)
**Estimated Effort:** 3-4 sprints
**Status:** Planning

---

## Overview

The `with` statement provides automatic resource management through context managers, ensuring proper setup and cleanup of resources like files, database connections, locks, etc.

### Syntax

```simple
# Basic usage
with open("file.txt") as f:
    data = f.read()
    # f is automatically closed when block exits

# Multiple context managers
with open("input.txt") as inp, open("output.txt") as out:
    data = inp.read()
    out.write(data)

# No variable binding
with lock():
    # critical section
    pass

# Nested contexts
with database.transaction() as tx:
    with tx.cursor() as cursor:
        cursor.execute("SELECT * FROM users")
```

---

## Python Context Manager Protocol

The context manager protocol requires two methods:

```simple
class ContextManager:
    fn __enter__() -> T:
        """Called when entering the with block"""
        # Setup code
        return resource

    fn __exit__(exc_type, exc_value, traceback) -> bool:
        """Called when exiting the with block"""
        # Cleanup code
        # Return true to suppress exception, false to propagate
        return false
```

---

## Simple Language Design

### Option 1: Python-style Protocol

Use `__enter__` and `__exit__` methods:

```simple
class File:
    path: text
    handle: FileHandle

    fn __enter__() -> File:
        self.handle = open_file(self.path)
        self

    fn __exit__(exc_type, exc_value, traceback) -> bool:
        self.handle.close()
        false  # Don't suppress exceptions
```

**Pros:**
- Familiar to Python developers
- Clear separation of enter/exit logic
- Can suppress exceptions

**Cons:**
- Requires exception system (not yet implemented)
- Magic method naming convention

### Option 2: Simple Resource Protocol

Use `enter()` and `cleanup()` methods with simpler signature:

```simple
class File:
    path: text
    handle: FileHandle

    fn enter() -> File:
        self.handle = open_file(self.path)
        self

    fn cleanup():
        self.handle.close()
```

**Pros:**
- Simpler API
- No exception handling required
- Works with current runtime

**Cons:**
- Can't suppress exceptions
- Less control over cleanup behavior

### Option 3: Trait-based Protocol

Define a `Context` trait:

```simple
trait Context<T>:
    fn enter() -> T
    fn cleanup()

impl Context<File> for File:
    fn enter() -> File:
        self.handle = open_file(self.path)
        self

    fn cleanup():
        self.handle.close()
```

**Pros:**
- Type-safe
- Explicit protocol
- Can add multiple context implementations

**Cons:**
- More verbose
- Requires trait system maturity

---

## Recommended Approach: Option 2 (Simple Resource Protocol)

Start with the simpler `enter()` and `cleanup()` protocol, which works with the current runtime and doesn't require exception handling.

### Implementation Phases

---

## Phase 1: Parser Support (1 sprint)

### AST Node

```simple
struct WithStmt:
    items: [WithItem]      # List of context managers
    body: [Stmt]           # Block body

struct WithItem:
    context_expr: Expr     # Expression that produces context manager
    target: Option<text>   # Optional variable binding (the "as" part)
```

### Lexer Changes

Add `with` as a keyword:
- `with` token type
- `as` keyword (if not already present)

### Parser Changes

Add `parse_with_stmt()`:

```simple
fn parse_with_stmt() -> WithStmt:
    consume(Keyword("with"))

    var items = []
    loop:
        val context_expr = parse_expr()

        var target = nil
        if current_token() == Keyword("as"):
            consume(Keyword("as"))
            target = consume(Identifier).value

        items.push(WithItem(context_expr, target))

        if current_token() != Comma:
            break
        consume(Comma)

    consume(Colon)
    val body = parse_block()

    WithStmt(items, body)
```

---

## Phase 2: Semantic Analysis (0.5 sprint)

### Type Checking

1. Verify context expression has `enter()` and `cleanup()` methods
2. Check return type of `enter()` matches variable binding type
3. Validate block body type checking

```simple
fn check_with_stmt(stmt: WithStmt, env: TypeEnv):
    for item in stmt.items:
        # Check context expression has required methods
        val ctx_type = infer_type(item.context_expr, env)

        if not has_method(ctx_type, "enter"):
            error("Type {ctx_type} does not implement enter() method")

        if not has_method(ctx_type, "cleanup"):
            error("Type {ctx_type} does not implement cleanup() method")

        # If variable binding, add to environment
        if item.target.?:
            val enter_return_type = get_method_return_type(ctx_type, "enter")
            env.add_binding(item.target, enter_return_type)

    # Check body with updated environment
    check_block(stmt.body, env)
```

---

## Phase 3: Interpreter Support (1 sprint)

### Desugaring Approach

Transform `with` statement into try-finally equivalent:

```simple
# Original:
with open("file.txt") as f:
    data = f.read()

# Desugared (conceptual - no try/finally yet):
__ctx1 = open("file.txt")
f = __ctx1.enter()
try:
    data = f.read()
finally:
    __ctx1.cleanup()
```

### Without Exception Handling

Since we don't have try/finally yet, we need a simpler approach:

```simple
# Desugar to:
__ctx1 = open("file.txt")
f = __ctx1.enter()
__with_error = nil

# Execute body
data = f.read()

# Always cleanup
__ctx1.cleanup()

# Re-raise error if one occurred
if __with_error != nil:
    raise __with_error
```

### Interpreter Implementation

```simple
fn eval_with_stmt(stmt: WithStmt, env: Env) -> Value:
    var cleanup_fns = []

    # Enter all contexts
    for item in stmt.items:
        val ctx_value = eval_expr(item.context_expr, env)

        # Call enter() method
        val enter_method = get_method(ctx_value, "enter")
        val resource = call_method(enter_method, ctx_value, [])

        # Bind to variable if specified
        if item.target.?:
            env.set(item.target, resource)

        # Store cleanup function
        val cleanup_method = get_method(ctx_value, "cleanup")
        cleanup_fns.push((cleanup_method, ctx_value))

    var error = nil
    var result = nil

    # Execute body
    try:
        result = eval_block(stmt.body, env)
    catch e:
        error = e

    # Always cleanup in reverse order
    for (cleanup_fn, ctx) in cleanup_fns.reverse():
        call_method(cleanup_fn, ctx, [])

    # Re-raise error if one occurred
    if error != nil:
        raise error

    result
```

---

## Phase 4: Standard Library Support (1 sprint)

### File Context Manager

```simple
# src/lib/io/file.spl
class File:
    path: text
    handle: i64
    is_open: bool

    fn enter() -> File:
        self.handle = rt_file_open(self.path)
        self.is_open = true
        self

    fn cleanup():
        if self.is_open:
            rt_file_close(self.handle)
            self.is_open = false

    fn read() -> text:
        if not self.is_open:
            error("File is not open")
        rt_file_read(self.handle)

    fn write(data: text):
        if not self.is_open:
            error("File is not open")
        rt_file_write(self.handle, data)

# Usage:
fn open(path: text) -> File:
    File(path: path, handle: 0, is_open: false)

# Example:
with open("data.txt") as f:
    content = f.read()
    print content
```

### Lock Context Manager

```simple
# src/lib/concurrency/lock.spl
class Lock:
    id: i64
    is_locked: bool

    fn enter() -> Lock:
        rt_lock_acquire(self.id)
        self.is_locked = true
        self

    fn cleanup():
        if self.is_locked:
            rt_lock_release(self.id)
            self.is_locked = false

# Usage:
mutex = Lock(id: 1, is_locked: false)

with mutex:
    # critical section
    shared_data.update()
```

### Database Transaction

```simple
# src/lib/database/transaction.spl
class Transaction:
    db: Database
    is_active: bool

    fn enter() -> Transaction:
        rt_db_begin_transaction(self.db)
        self.is_active = true
        self

    fn cleanup():
        if self.is_active:
            rt_db_rollback(self.db)
            self.is_active = false

    fn commit():
        if self.is_active:
            rt_db_commit(self.db)
            self.is_active = false

    fn rollback():
        if self.is_active:
            rt_db_rollback(self.db)
            self.is_active = false

# Usage:
with db.transaction() as tx:
    tx.execute("INSERT INTO users ...")
    tx.execute("UPDATE stats ...")
    tx.commit()  # Explicit commit
    # If commit() not called, automatic rollback in cleanup()
```

---

## Phase 5: Testing & Documentation (0.5 sprint)

### Test Cases

1. **Basic file operations**
   ```simple
   with open("test.txt") as f:
       data = f.read()
   ```

2. **Multiple context managers**
   ```simple
   with open("in.txt") as inp, open("out.txt") as out:
       out.write(inp.read())
   ```

3. **Nested contexts**
   ```simple
   with lock1:
       with lock2:
           # critical section
   ```

4. **Cleanup on error**
   ```simple
   with open("file.txt") as f:
       f.write("data")
       error("Something went wrong")
       # Cleanup still called
   ```

5. **No variable binding**
   ```simple
   with timer():
       expensive_operation()
   ```

---

## Compatibility & Migration

### Backward Compatibility

No breaking changes - this is a new feature.

### Migration Path

Existing code using manual cleanup:

```simple
# Before:
file = open("data.txt")
data = file.read()
file.close()

# After:
with open("data.txt") as file:
    data = file.read()
# Automatic close
```

---

## Alternative: Defer Statement

Instead of full `with` statement, consider a simpler `defer` statement (Go-style):

```simple
fn process_file():
    file = open("data.txt")
    defer file.close()  # Called when function returns

    data = file.read()
    return data
```

**Pros:**
- Simpler implementation
- No new protocol needed
- Clear cleanup point

**Cons:**
- Function-scoped only (not block-scoped)
- Less structured than `with`
- Can't bind variables like `as` clause

**Recommendation:** Implement both - `defer` first (easier), then `with` later.

---

## Success Criteria

1. ✅ Parser accepts `with` statement syntax
2. ✅ Type checker validates context manager protocol
3. ✅ Interpreter correctly calls enter/cleanup methods
4. ✅ Cleanup happens even on errors
5. ✅ Multiple context managers work correctly
6. ✅ Standard library has File, Lock, Transaction context managers
7. ✅ 531 skipped tests now pass
8. ✅ Documentation and examples complete

---

## Dependencies

- **Blocker:** None (can implement with current runtime)
- **Enhanced by:** Exception handling (for better error propagation)
- **Enables:** Resource management patterns, RAII-style programming

---

## Risk Analysis

**Low Risk:**
- Parser changes are straightforward
- Protocol is simple (2 methods)
- Can test incrementally

**Medium Risk:**
- Cleanup must happen in all code paths (error/return/break)
- Need careful testing of cleanup order

**Mitigation:**
- Start with simple cases (single context manager)
- Add comprehensive test coverage
- Validate cleanup happens in all scenarios

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 1. Parser | 1 week | `with` syntax accepted |
| 2. Semantic | 2-3 days | Type checking works |
| 3. Interpreter | 1 week | Basic execution works |
| 4. Stdlib | 1 week | File, Lock, Transaction |
| 5. Testing | 2-3 days | All tests pass |
| **Total** | **3-4 weeks** | **Feature complete** |

---

## Next Steps

1. ✅ Create this implementation plan
2. ⏳ Review plan with team
3. ⏳ Add `with` keyword to lexer
4. ⏳ Implement parser support
5. ⏳ Add semantic analysis
6. ⏳ Implement interpreter
7. ⏳ Add stdlib context managers
8. ⏳ Enable skipped tests
