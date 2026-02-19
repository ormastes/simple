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

1. Add variant to the type system in `src/compiler_core/types.spl`
2. Create separate module for complex types
3. Update type substitution for new variants
4. Update `contains_var()` if type can contain variables
5. Export public API through module declarations

Example:
```simple
# src/compiler_core/types.spl
enum Type:
    # ... existing variants
    NewType(name: text)   # Add new variant

# src/compiler_core/new_type.spl
class NewType:
    name: text
    fields: [Field]
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

## Advanced Features

### MDSOC (Multi-Dimensional Separation of Concerns)

**Location:** `src/compiler/mdsoc/`

Virtual capsules with manifest-composed hypermodules (inspired by Hyper/J, FOP/AHEAD):

**3-Tier Visibility:**
```simple
enum CapsuleVisibility:
    Public      # Visible everywhere (via surface)
    Internal    # Visible within same virtual capsule
    Private     # Visible within same caret + folder
```

**Key Concepts:**
- **Caret** (^): Aspect root namespace (^core, ^ui, ^infra)
- **Virtual Capsule**: Composed module with explicit surface
- **Layer Enforcement**: Directional dependency constraints
- **Surface Binding**: Explicit capsule interface exports

**Example:**
```simple
use compiler.mdsoc.types.{CapsuleVisibility, VirtualCapsule}

val visibility = CapsuleVisibility.Internal
check(visibility.is_internal())  # true
```

**Modules:**
- `types.spl` - Core type definitions (CapsuleVisibility, CaretId, LayerDef)
- `config.spl` - SDN config parser for capsule.sdn
- `layer_checker.spl` - Layer dependency enforcement

**Tests:** `test/unit/compiler/mdsoc/` (3 passing)

### Public Interface Documentation

**Location:** `src/app/doc/public_check/`

Validates documentation on exported types (structs, classes, enums, functions):

**Features:**
- Parse `export X, Y, Z` statements from mod.spl or __init__.spl
- Find type definitions in source files
- Extract docstrings (triple-quoted `"""` or `#` comments)
- Report missing documentation with file:line references

**Example:**
```simple
use app.doc.public_check.export_parser.{find_module_exports}
use app.doc.public_check.docstring_checker.{check_module_docstrings}

# Find all exported types
val exports = find_module_exports("src/std/array")

# Check which have docstrings
val export_names = exports.map(\e: e.name)
val docs = check_module_docstrings("src/std/array", export_names)

# Report missing
for info in docs:
    if not info.has_docstring:
        print "Missing doc: {info.type_name} ({info.type_kind})"
```

**Modules:**
- `export_parser.spl` - Parse export statements
- `docstring_checker.spl` - Extract and validate docstrings
- `statistics.spl` - Coverage metrics
- `warnings.spl` - Missing documentation warnings

**Tests:** `test/unit/app/doc/public_check/` (2 passing)

**Integration:** Can be combined with MDSOC to validate documentation on `CapsuleVisibility.Public` exports.

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
