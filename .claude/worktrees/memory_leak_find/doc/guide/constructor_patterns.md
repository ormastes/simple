# Constructor Patterns in Simple Language

## Python-Style Constructors

Simple uses Python-style constructors where calling `ClassName()` automatically invokes the `fn new()` method if defined:

```simple
struct Point:
    x: i64
    y: i64

    fn new(x: i64, y: i64) -> Point:
        return Point(x: x, y: y)

# Call using Python-style syntax
val p = Point(3, 4)  # Automatically calls Point.new(3, 4)
```

## How It Works

**Definition**: Add `fn new()` method inside your struct/class
**Call**: Use `ClassName(args)` - it automatically calls `ClassName.new(args)`

```simple
struct Channel:
    _id: i64

    fn new() -> Channel:
        val id = rt_channel_new()  # FFI call
        return Channel(_id: id)

# Usage - automatically calls Channel.new()
val ch = Channel()
```

## Construction Patterns

### 1. Simple Constructor (No Parameters)

```simple
struct Counter:
    value: i32

    fn new() -> Counter:
        return Counter(value: 0)

# Call it
val c = Counter()  # Calls Counter.new()
```

### 2. Constructor with Parameters

```simple
struct BoundedChannel<T>:
    capacity: i32
    buffer: List<T>
    closed: bool

    fn new(capacity: i32) -> BoundedChannel<T>:
        return BoundedChannel(
            capacity: capacity,
            buffer: [],
            closed: false
        )

# Call with parameter
val ch = BoundedChannel(10)  # Calls BoundedChannel.new(10)
```

### 3. FFI-Backed Constructor

```simple
struct Channel:
    _id: i64

    fn new() -> Channel:
        val id = rt_channel_new()  # Call FFI to get handle
        return Channel(_id: id)

# Usage
val ch = Channel()  # FFI called inside new()
```

### 4. Constructor with Complex Logic

```simple
struct Config:
    timeout: i64
    retries: i64
    validated: bool

    fn new(timeout: i64, retries: i64) -> Config:
        # Validation logic
        val t = if timeout < 0: 30 else: timeout
        val r = if retries < 1: 3 else: retries

        return Config(
            timeout: t,
            retries: r,
            validated: true
        )

# Usage
val cfg = Config(60, 5)  # Validation happens in new()
```

### 5. Helper Functions for Convenience

You can provide helper functions for common construction patterns:

```simple
struct UnboundedChannel<T>:
    buffer: List<T>
    closed: bool

    fn new() -> UnboundedChannel<T>:
        return UnboundedChannel(buffer: [], closed: false)

# Helper function for creating sender/receiver pair
fn channel():
    val ch = UnboundedChannel()  # Calls UnboundedChannel.new()
    return (ch, ch)  # Return as (tx, rx) tuple

# Usage
val (tx, rx) = channel()
```

## Direct Construction vs new()

You can still use direct field construction when you don't need a `new()` method:

```simple
struct Point:
    x: i64
    y: i64

# Direct construction - no new() method needed
val p = Point(x: 3, y: 4)
```

But if you define a `new()` method, it will be called instead:

```simple
struct Point:
    x: i64
    y: i64

    fn new(x: i64, y: i64) -> Point:
        print "Point created!"
        return Point(x: x, y: y)

# This calls new(), which prints "Point created!"
val p = Point(3, 4)
```

## Generic Types

For generic types, `new()` allows type inference:

```simple
struct Container<T>:
    value: T

    fn new(val: T) -> Container<T>:
        return Container(value: val)

# Type T is inferred from the argument
val c = Container(42)  # T = i32
val s = Container("hello")  # T = text
```

## Summary

| Pattern | Definition | Call | Example |
|---------|------------|------|---------|
| **No constructor** | Just fields | Direct | `Point(x: 3, y: 4)` |
| **Simple constructor** | `fn new()` | `ClassName()` | `Counter()` → calls `Counter.new()` |
| **With parameters** | `fn new(args)` | `ClassName(args)` | `Config(60, 5)` → calls `Config.new(60, 5)` |
| **FFI-backed** | `fn new()` with FFI | `ClassName()` | `Channel()` → calls FFI inside `new()` |
| **Generic** | `fn new<T>(val: T)` | `Container(val)` | Type inferred from argument |

**Key Rule**:
- **Define**: `fn new(args) -> TypeName` inside your struct/class
- **Call**: `TypeName(args)` - automatically invokes `TypeName.new(args)`

This is Python-style: you call the type name as if it's a function, and it automatically calls the `new()` method.
