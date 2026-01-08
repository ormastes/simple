# Type System Features - Design TODOs

**Status:** Design Required
**Related:** `doc/spec/traits.md`, `doc/spec/types.md`, `doc/spec/data_structures.md`

---

## Design TODO List

| Feature | Priority | Difficulty | Status | Spec File |
|---------|----------|------------|--------|-----------|
| Mixins | High | 4 | 🔄 75% Complete | `research/mixins_strongly_typed.md` |
| Implements Traits | High | 3 | 🔄 In Progress | `spec/traits.md` |
| Impl Blocks | High | 2 | ✅ Complete (parser) | `spec/traits.md` |
| Union Types | High | 3 | 📋 Design Required | `spec/types.md` |
| Result/Option | High | 2 | 📋 Design Required | `spec/types.md` |
| Bitfields | Medium | 3 | 📋 Design Required | (new) |

---

## 0. Mixins (Strongly-Typed Composition)

**Current Status:** 75% Complete (Parser, Type System, HIR complete; Testing in progress)

### Implementation Tasks

**Phase 1: Grammar and Parser** ✅ Complete
- [x] Mixin keyword and `MixinDef` AST node
- [x] Generic parameters (`mixin Name<T>`)
- [x] Trait bounds (`where T: Trait`)
- [x] Field definitions (`field name: Type`)
- [x] Method definitions
- [x] Required method declarations
- [x] Mixin application syntax (`use MixinName`)
- [x] `MixinRef` AST node with type arguments
- [x] Parser tests

**Phase 2: Type System** ✅ Complete
- [x] Mixin type representation in `simple-type`
- [x] Type parameter substitution
- [x] Trait bound checking
- [x] Required method verification
- [x] Field conflict detection
- [x] Type inference integration (Algorithm W)
- [x] Unit tests

**Phase 3: HIR Lowering** ✅ Complete
- [x] `HirType::Mixin` variant
- [x] `HirMixinMethod` structure
- [x] `register_mixin()` implementation
- [x] Field expansion in `register_class()`
- [x] Method lowering in second pass
- [x] Type registry updates
- [x] Pattern match updates in codegen
- [x] Lean code generation

**Phase 4: Testing** 🚧 In Progress
- [ ] Parser unit tests
- [ ] Type system integration tests
- [ ] HIR lowering tests
- [ ] End-to-end tests (.simple files)
- [ ] BDD/Gherkin feature tests
- [ ] Error handling tests
- [ ] Performance benchmarks

**Phase 5: Optimization** 📋 Planned
- [ ] Method inlining
- [ ] Dead code elimination
- [ ] Memory layout optimization
- [ ] Better error messages
- [ ] IDE integration (LSP)

### Syntax Examples

```simple
# Basic mixin
mixin Timestamped {
    field created_at: i64
    field updated_at: i64
    
    fn get_age() -> i64 {
        self.updated_at - self.created_at
    }
}

# Generic mixin with trait bounds
mixin Container<T> where T: Clone {
    field items: [T]
    
    fn add(item: T) {
        self.items.push(item.clone())
    }
    
    fn size() -> i32 {
        self.items.len()
    }
}

# Mixin with required methods
mixin Serializable {
    fn to_json() -> str  # Required: class must implement
    
    fn serialize() -> str {  # Provided: implemented by mixin
        "{ \"data\": " + self.to_json() + " }"
    }
}

# Mixin application
class Document {
    field title: str
    field content: str
    
    use Timestamped
    use Serializable
    
    # Implement required method
    fn to_json() -> str {
        "{\"title\": \"" + self.title + "\", \"content\": \"" + self.content + "\"}"
    }
}

# Multiple mixins
class User {
    field name: str
    use Identifiable
    use Timestamped
    use Auditable
}
```

### Design Decisions

1. **Flattening at HIR Level:** Mixins are expanded into classes during HIR lowering, so MIR sees only regular fields and methods
2. **Static Dispatch:** All mixin methods resolved at compile time (no vtable overhead)
3. **Nominal Typing:** Classes using the same mixin are NOT subtypes of each other
4. **LL(1) Grammar:** Each production starts with unique keyword (`mixin`, `use`, `field`, `fn`)
5. **Type Inference:** Seamless integration with Hindley-Milner type inference

### Key Properties

- **Type Safety:** All errors caught at compile time
- **Zero-Cost:** Flattening eliminates runtime overhead
- **Composable:** Multiple mixins per class
- **Generic:** Full parametric polymorphism support
- **Verified:** Formal proofs via Lean

### Related Files

- `src/parser/src/statements/mixins.rs` - Parsing
- `src/parser/src/ast/nodes/definitions.rs` - AST nodes
- `src/type/src/mixin.rs` - Type representation
- `src/compiler/src/hir/types/type_system.rs` - HIR types
- `src/compiler/src/hir/lower/module_lowering.rs` - Lowering
- `verification/lean/simple/TypeSystem/Mixins.lean` - Formal verification
- `doc/research/mixins_strongly_typed.md` - Complete design document
- `doc/implementation_summary_phase{1,2,3,4}_mixin_{parser,types,hir,testing}.md`

---

## 1. Implements Traits

**Current Status:** Parser complete, dynamic dispatch pending

### Implementation Tasks
- [x] Trait definition parsing (`trait Name:`)
- [x] Method signature parsing (required vs default)
- [x] `impl Trait for Type` parsing
- [x] Static dispatch (monomorphization)
- [ ] Dynamic dispatch (vtable generation)
- [ ] Trait object types (`dyn Trait`)
- [ ] Trait bounds in generics (`T: Trait`)
- [ ] Multiple trait bounds (`T: Trait1 + Trait2`)
- [ ] Associated types in traits
- [ ] Associated constants in traits

### Design Questions
1. How to handle diamond problem (trait A extends B, trait C extends B)?
2. Should we support negative trait bounds (`T: !Trait`)?
3. Auto-trait implementation (like Rust's `Send`/`Sync`)?

### Related Files
- `src/parser/src/statements/traits.rs` - parsing
- `src/compiler/src/hir/traits.rs` - HIR representation
- `src/compiler/src/monomorphize/` - static dispatch

---

## 2. Impl Blocks

**Current Status:** Parser complete, method dispatch working

### Implementation Tasks
- [x] Inherent impl blocks (`impl Type:`)
- [x] Trait impl blocks (`impl Trait for Type:`)
- [x] Method dispatch in interpreter
- [x] Self type resolution
- [ ] Extension methods (impl for external types)
- [ ] Blanket implementations (`impl<T> Trait for T`)
- [ ] Specialization (overlapping impls)
- [ ] Coherence rules (orphan rule)

### Design Questions
1. Allow impl blocks in separate modules from type definition?
2. How strict should the orphan rule be?
3. Support conditional implementations (`impl<T: Clone> Clone for Vec[T]`)?

---

## 3. Union Types

**Current Status:** Not implemented

### Proposed Syntax

```simple
# Tagged union (discriminated)
union Shape:
    Circle(radius: f64)
    Rectangle(width: f64, height: f64)
    Triangle(a: f64, b: f64, c: f64)

# Usage
let s: Shape = Shape.Circle(radius: 5.0)

match s:
    case Circle(r): area = 3.14 * r * r
    case Rectangle(w, h): area = w * h
    case Triangle(a, b, c): area = heron(a, b, c)
```

### Implementation Tasks
- [ ] Union type declaration parsing
- [ ] Variant constructors (`Shape.Circle(...)`)
- [ ] Discriminant storage (tag field)
- [ ] Pattern matching integration
- [ ] Exhaustiveness checking
- [ ] Runtime representation (`RuntimeEnum` extension)
- [ ] MIR instructions (EnumDiscriminant, EnumVariant)
- [ ] Impl blocks for unions
- [ ] Trait implementations for unions

### Impl Blocks for Unions

```simple
union Shape:
    Circle(radius: f64)
    Rectangle(width: f64, height: f64)

# Inherent impl block - add methods to union
impl Shape:
    fn area(self) -> f64:
        match self:
            case Circle(r): return 3.14159 * r * r
            case Rectangle(w, h): return w * h

    fn scale(self, factor: f64) -> Shape:
        match self:
            case Circle(r): return Shape.Circle(radius: r * factor)
            case Rectangle(w, h): return Shape.Rectangle(width: w * factor, height: h * factor)

    # Associated function (constructor helper)
    fn unit_circle() -> Shape:
        return Shape.Circle(radius: 1.0)

# Usage
let s = Shape.Circle(radius: 5.0)
print s.area()           # 78.54
let s2 = s.scale(2.0)    # Circle with radius 10.0
let uc = Shape.unit_circle()
```

### Trait Implementations for Unions

```simple
trait Drawable:
    fn draw(self)

impl Drawable for Shape:
    fn draw(self):
        match self:
            case Circle(r):
                draw_circle(r)
            case Rectangle(w, h):
                draw_rect(w, h)

# Derive common traits
#[derive(Eq, Clone, Debug)]
union Option[T]:
    Some(value: T)
    None
```

### Variant-Specific Methods (Planned)

```simple
union Result[T, E]:
    Ok(value: T)
    Err(error: E)

impl Result[T, E]:
    # Methods on specific variants
    fn Ok.get(self) -> T:
        return self.value

    fn Err.get(self) -> E:
        return self.error

    # Or using pattern guards
    fn unwrap(self) -> T:
        match self:
            case Ok(v): return v
            case Err(e): panic("unwrap on Err: {e}")
```

### Design Questions
1. Naming: `union` vs `enum` vs `variant`?
2. Support untagged unions (C-style, unsafe)?
3. Recursive unions (tree structures)?
4. Empty variants (`None` with no data)?
5. Variant-specific methods syntax?
6. Auto-derive for common traits (Eq, Clone, Debug)?

### Related to Existing
- Current `enum` in Simple is value-only (no associated data)
- This extends to full algebraic data types

---

## 4. Result/Option Types

**Current Status:** Partial - error unions exist but no dedicated types

### Proposed Design

```simple
# Option type (nullable)
type Option[T] = union:
    Some(value: T)
    None

# Result type (fallible)
type Result[T, E] = union:
    Ok(value: T)
    Err(error: E)

# Shorthand syntax
fn read_file(path: str) -> str?        # equivalent to Option[str]
fn parse_int(s: str) -> i64 | ParseError  # equivalent to Result[i64, ParseError]
```

### Implementation Tasks
- [ ] Define `Option[T]` in stdlib (`std/core/option.spl`)
- [ ] Define `Result[T, E]` in stdlib (`std/core/result.spl`)
- [ ] `?` operator for Option (return None on None)
- [ ] `?` operator for Result (propagate error)
- [ ] `unwrap()`, `expect()`, `map()`, `and_then()` methods
- [ ] `if let Some(x) = opt:` syntax
- [ ] `match` exhaustiveness for Option/Result

### Design Questions
1. Should `nil` be distinct from `Option.None`?
2. Support implicit Option wrapping (like TypeScript's optional)?
3. Error chaining and context addition?
4. `try`/`catch` vs explicit Result handling?

### Standard Library Methods

```simple
# Option methods
impl Option[T]:
    fn is_some() -> bool
    fn is_none() -> bool
    fn unwrap() -> T           # panics if None
    fn unwrap_or(default: T) -> T
    fn map[U](f: fn(T) -> U) -> Option[U]
    fn and_then[U](f: fn(T) -> Option[U]) -> Option[U]
    fn filter(predicate: fn(T) -> bool) -> Option[T]

# Result methods
impl Result[T, E]:
    fn is_ok() -> bool
    fn is_err() -> bool
    fn unwrap() -> T           # panics if Err
    fn unwrap_err() -> E       # panics if Ok
    fn map[U](f: fn(T) -> U) -> Result[U, E]
    fn map_err[F](f: fn(E) -> F) -> Result[T, F]
    fn and_then[U](f: fn(T) -> Result[U, E]) -> Result[U, E]
```

---

## 5. Bitfields

**Current Status:** Not designed

### Proposed Syntax

```simple
# Packed bitfield struct
bitfield Flags(u8):
    readable: 1      # bit 0
    writable: 1      # bit 1
    executable: 1    # bit 2
    _reserved: 5     # bits 3-7 (padding)

# Usage
let f = Flags(readable: 1, writable: 1, executable: 0)
f.readable = 0       # set bit
let can_write = f.writable  # get bit

# Multi-bit fields
bitfield Color(u32):
    red: 8           # bits 0-7
    green: 8         # bits 8-15
    blue: 8          # bits 16-23
    alpha: 8         # bits 24-31
```

### Implementation Tasks
- [ ] Bitfield declaration parsing (`bitfield Name(backing):`)
- [ ] Field width specification
- [ ] Automatic offset calculation
- [ ] Getter/setter generation (bit masking)
- [ ] Packed representation guarantee
- [ ] Validation (fields fit in backing type)
- [ ] MIR instructions for bit manipulation
- [ ] FFI compatibility (C struct packing)

### Design Questions
1. Big-endian vs little-endian field order?
2. Allow signed bit fields?
3. Support spanning across byte boundaries?
4. Alignment requirements?
5. Named constants for field values?

### Use Cases
- Hardware register access
- Network protocol headers
- Compact data structures
- FFI with C bitfields
- Flags/permissions

---

## Implementation Order

### Phase 1: Foundation
1. **Union Types** - Required for Option/Result
2. **Result/Option** - Core error handling

### Phase 2: Trait Completion
3. **Dynamic Dispatch** - Complete trait implementation
4. **Impl Blocks** - Extension methods, blanket impls

### Phase 3: Low-Level
5. **Bitfields** - Hardware/FFI support

---

## Related Documentation

- `doc/spec/traits.md` - Trait specification
- `doc/spec/types.md` - Type system specification
- `doc/spec/data_structures.md` - Struct/class/enum specification
- `doc/features/feature.md` - Feature overview
- `doc/FEATURE_STATUS.md` - Implementation status

---

## References

- Rust: `enum`, `Option`, `Result`, traits, bitflags crate
- Haskell: ADTs, type classes
- OCaml: variant types, modules
- C: unions, bitfields
- TypeScript: union types, optional chaining
