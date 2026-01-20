# Stdlib Skill - Simple Standard Library Development

## Directory Structure

```
simple/std_lib/
├── src/                    # Source modules
│   ├── __init__.spl        # Root manifest
│   ├── core/               # GC + mutable (default)
│   ├── core_immut/         # GC + immutable
│   ├── core_nogc/          # No GC + mutable
│   ├── core_nogc_immut/    # No GC + immutable
│   ├── host/               # OS-based overlays
│   │   └── async_nogc_mut/ # DEFAULT variant
│   ├── concurrency/        # Actors, channels, threads
│   ├── simd/               # SIMD & vector math
│   ├── spec/               # BDD framework
│   ├── doctest/            # Doctest framework
│   └── units/              # Semantic types (ByteCount, etc)
└── test/                   # Tests (mirrors src/)
    ├── unit/               # Unit tests by module
    ├── system/             # Framework tests
    ├── integration/        # Cross-module tests
    └── fixtures/           # Test data
```

## Variant System

### Memory Model Matrix

| Directory | GC | Mutable | Use Case |
|-----------|-----|---------|----------|
| `core/` | Yes | Yes | General purpose |
| `core_immut/` | Yes | No | Persistent data |
| `core_nogc/` | No | Yes | Performance critical |
| `core_nogc_immut/` | No | No | Static allocation |

### Host Variants

Default: `async_nogc_mut` (Async + NoGC + Mutable)

```
host/
├── async_gc_mut/      # Async + GC + Mutable
├── async_gc_immut/    # Async + GC + Immutable
├── async_nogc_mut/    # DEFAULT
├── sync_nogc_mut/     # Sync + NoGC + Mutable
└── common/            # Shared code
```

## Writing Stdlib Modules

### Module Structure
```simple
# src/mymodule/__init__.spl
"""
MyModule - Brief description.

Provides X, Y, Z functionality.
"""

requires [fs]  # Required capabilities

# Re-exports
pub use .types.*
pub use .functions.*
```

```simple
# src/mymodule/types.spl
"""Type definitions for MyModule."""

pub struct MyType:
    """A useful type."""
    value: Int
    name: String

    fn new(value: Int, name: String) -> MyType:
        return MyType(value=value, name=name)
```

### Capability-Based Effects

Declare required capabilities in `__init__.spl`:
```simple
requires [fs, net, io]
```

Available capabilities:
- `io` - Console I/O
- `fs` - File system
- `net` - Network
- `unsafe` - Unsafe operations
- `verify` - Verification context
- `trusted` - Trusted code

### Effect Decorators
```simple
@pure
fn add(a: Int, b: Int) -> Int:
    """Pure function - no side effects."""
    return a + b

@io
fn print_value(x: Int):
    """Requires io capability."""
    io.println("Value: {x}")

@fs
fn read_config(path: String) -> String:
    """Requires fs capability."""
    return fs.read_file(path)
```

## Writing Tests

Tests go in `test/` mirroring `src/` structure.

### Unit Test
```simple
# test/unit/mymodule/mytype_spec.spl
import spec
import mymodule

describe "MyType":
    """Tests for MyType."""

    context "construction":
        it "creates with values":
            let t = MyType.new(42, "test")
            expect(t.value).to(equal(42))
            expect(t.name).to(equal("test"))

    context "operations":
        before_each:
            self.t = MyType.new(10, "item")

        it "can modify value":
            self.t.value = 20
            expect(self.t.value).to(equal(20))
```

### Run Tests
```bash
# All stdlib tests
cargo test -p simple-driver simple_stdlib

# Unit tests only
cargo test -p simple-driver simple_stdlib_unit

# Specific module
cargo test -p simple-driver simple_stdlib_unit_mymodule

# Direct run
./target/debug/simple simple/std_lib/test/unit/mymodule/mytype_spec.spl
```

## Contracts

Use contracts for critical functions:
```simple
fn divide(a: Int, b: Int) -> Int:
    """Safe division with contract."""
    in: b != 0, "divisor must be non-zero"
    out(ret): ret * b <= a and ret * b > a - b
    return a / b

class BoundedBuffer[T>:
    items: List<T>
    capacity: Int

    invariant: self.items.len() <= self.capacity

    fn push(self, item: T):
        in: self.items.len() < self.capacity
        out: self.items.len() == old(self.items.len()) + 1
        self.items.append(item)
```

## Common Patterns

### Option/Result Types
```simple
# Already in stdlib
enum Option<T>:
    Some(value: T)
    None

enum Result<T, E>:
    Ok(value: T)
    Err(error: E)

# Usage
fn find(items: List<Int>, target: Int) -> Option<Int>:
    for i, item in items.enumerate():
        if item == target:
            return Some(i)
    return None
```

### Iterators
```simple
trait Iterator[T>:
    fn next(self) -> Option<T>

fn map[T, U>(self, f: fn(T) -> U) -> MapIterator[T, U>:
    return MapIterator(inner=self, f=f)
```

### Generic Collections
```simple
struct Vec[T>:
    data: Array[T>
    len: Int

    fn push(mut self, item: T):
        self.data[self.len] = item
        self.len += 1
```

## Bug Reports & Improvements

### Bug Report
File in `simple/bug_report.md`:
```markdown
### [stdlib/mymodule] Brief description
**Type:** Bug
**Priority:** High
**Description:** ...
**Reproduction:** ...
```

### Improvement Request
File in `simple/improve_request.md`:
```markdown
### [stdlib/mymodule] Add feature X
**Type:** Improvement
**Priority:** Medium
**Description:** ...
**Proposed API:** ...
```

## See Also

- `simple/std_lib/README.md` - Full stdlib docs
- `doc/spec/stdlib.md` - Stdlib specification
- `doc/spec/testing/testing_bdd_framework.md` - BDD framework
- `.claude/skills/test.md` - Test writing skill
