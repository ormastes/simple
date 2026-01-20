# Design Skill - Simple Language

## Design Principles

### Keep It Simple
- Minimum complexity for current task
- No hypothetical future requirements
- Prefer explicit over implicit
- Favor composition over inheritance

### API Design
- Consistent naming across modules
- Predictable behavior
- Clear error messages
- Minimal surface area

## Type System Design

### Adding New Types

1. Add variant to `Type` enum in `src/type/src/lib.rs`
2. Create separate module for complex types
3. Update `Type::apply_subst()` for new variants
4. Update `contains_var()` if type can contain variables
5. Export public API through module declarations

Example:
```rust
// src/type/src/lib.rs
pub enum Type {
    // ... existing variants
    NewType(String),  // Add new variant
}

// src/type/src/new_type.rs
pub struct NewType {
    pub name: String,
    pub fields: Vec<Field>,
}
```

### Memory Model

Reference capabilities:
- `T` - Shared (immutable) reference
- `mut T` - Exclusive (mutable) reference
- `iso T` - Isolated (transferable ownership)

Concurrency modes:
- `actor` - Actor model with message passing
- `lock_base` - Traditional locks
- `unsafe` - Manual management

## Module Design

### Module System
```
package/
├── __init__.spl     # Package manifest with requires
├── core.spl         # Core functionality
├── utils.spl        # Utilities
└── sub/
    ├── __init__.spl # Subpackage manifest
    └── feature.spl
```

### Capability-Based Effects
```simple
# __init__.spl
requires [fs, net]   # Module requires these capabilities

# module.spl
@fs
fn read_file(path: String) -> String:
    ...

@net
fn fetch_url(url: String) -> Response:
    ...
```

## Pattern Decisions

### When to Use Each Pattern

**Enums with variants:**
```simple
enum Result<T, E>:
    Ok(value: T)
    Err(error: E)
```

**Structs for data:**
```simple
struct Point:
    x: Int
    y: Int
```

**Classes for behavior:**
```simple
class Connection:
    socket: Socket

    fn send(self, data: Bytes):
        self.socket.write(data)
```

**Traits for abstraction:**
```simple
trait Readable:
    fn read(self, n: Int) -> Bytes
```

## IR Design Levels

```
Source → AST → HIR → MIR → Codegen
         ↓      ↓     ↓
       Parse  Type  Effect   Machine
             Check  Track    Code
```

- **AST**: Syntax tree (parser output)
- **HIR**: Type-checked IR
- **MIR**: 50+ instructions with effects
- **Codegen**: Cranelift/LLVM backends

## Documentation

Design decisions go in:
- `doc/design/` - Architecture decisions
- `doc/spec/` - Language specifications
- `doc/research/` - Research and exploration

## See Also

- **`doc/guide/design_writing.md`** - Design writing guide (Draft→Test→Generate→Replace)
- **`doc/guide/architecture_writing.md`** - Architecture writing guide (Skeleton→Verify→Diagram)
- `doc/architecture/README.md` - Architecture overview
- `doc/design/memory.md` - Memory model design
- `doc/design/type_inference.md` - Type inference design
- `doc/spec/README.md` - Language specifications
