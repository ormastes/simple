# Simple Language Compiler Architecture

**Version:** 1.0
**Last Updated:** 2026-01-28

## Table of Contents

1. [Overview](#overview)
2. [Compilation Pipeline](#compilation-pipeline)
3. [Key Components](#key-components)
4. [Intermediate Representations](#intermediate-representations)
5. [Type System](#type-system)
6. [Monomorphization](#monomorphization)
7. [Code Generation](#code-generation)
8. [Module System](#module-system)

---

## Overview

The Simple compiler is a multi-stage compiler that transforms Simple source code into native executables or bytecode modules (.smf files). It supports multiple compilation modes:

- **Interpret**: Tree-walking interpreter for rapid development
- **JIT**: Just-In-Time compilation for interactive execution
- **AOT**: Ahead-Of-Time compilation to native binaries
- **Check**: Type checking only (no code generation)
- **SDN**: Safe data parsing mode (no code execution)

### Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         Source Code (.spl)                      │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │      Lexer       │ ← Token stream
                    └──────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │      Parser      │ ← AST
                    └──────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │  Block Resolver  │ ← Custom blocks
                    └──────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │   HIR Lowering   │ ← High-level IR
                    └──────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │  Type Inference  │ ← HM type inference
                    └──────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │  Monomorphizer   │ ← Generic specialization
                    └──────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │   MIR Lowering   │ ← Mid-level IR
                    └──────────────────┘
                              │
                ┌─────────────┴─────────────┐
                ↓                           ↓
      ┌──────────────────┐        ┌──────────────────┐
      │   Interpreter    │        │    Cranelift     │
      │   (Tree Walk)    │        │  (Native Code)   │
      └──────────────────┘        └──────────────────┘
                │                           │
                ↓                           ↓
       Direct Execution             ┌──────────────┐
                                    │  SMF Writer  │
                                    └──────────────┘
                                           │
                                           ↓
                                  .smf/.o/.exe File
```

---

## Compilation Pipeline

### Phase 1: Lexical Analysis

**Input**: Source code (`.spl` file)
**Output**: Token stream
**Module**: `simple/compiler/lexer.spl`

The lexer scans the source code and produces a stream of tokens. Key features:
- **Indentation-based syntax**: Tracks indentation levels for block structure
- **String interpolation**: Handles `"Hello {name}"` syntax
- **Math blocks**: Special lexing rules for `m{...}` expressions
- **Error recovery**: Reports multiple errors per file

**Example**:
```simple
fn add(a, b):
    a + b
```

**Tokens**:
```
[KEYWORD(fn), IDENT(add), LPAREN, IDENT(a), COMMA, IDENT(b), RPAREN, COLON,
 INDENT, IDENT(a), PLUS, IDENT(b), DEDENT, EOF]
```

### Phase 2: Parsing

**Input**: Token stream
**Output**: Abstract Syntax Tree (AST)
**Module**: `simple/compiler/parser.spl`

The parser builds an AST from tokens using recursive descent parsing. Key features:
- **Expression precedence**: Operator precedence climbing
- **Pattern matching**: Exhaustiveness checking
- **Generics**: `<>` syntax for type parameters
- **Error recovery**: Panic mode recovery

**AST Node Types**:
```simple
enum Node:
    Module(Module)
    Function(FunctionDef)
    Struct(StructDef)
    Class(ClassDef)
    Enum(EnumDef)
    Trait(TraitDef)
    Impl(ImplBlock)
    # ...expressions, statements...
```

### Phase 3: Block Resolution

**Input**: AST
**Output**: Resolved AST (with custom blocks expanded)
**Module**: `simple/compiler/blocks/resolver.spl`

Resolves custom block syntax (user-defined DSLs):
```simple
block my_dsl:
    syntax: "workflow {name}:"
    transform: \ast: expand_workflow(ast)
```

### Phase 4: HIR Lowering

**Input**: AST
**Output**: High-level Intermediate Representation (HIR)
**Module**: `simple/compiler/hir.spl`

Transforms AST into a typed intermediate form. Key features:
- **Name resolution**: Resolves identifiers to definitions
- **Scope tracking**: Manages lexical scopes
- **Trait resolution**: Links trait implementations
- **Effect tracking**: Tracks side effects (I/O, mutation)

**HIR Example**:
```simple
// Source
fn add(a: i32, b: i32) -> i32:
    a + b

// HIR
HirFunction {
    name: "add",
    params: [
        HirParam { name: "a", type_id: TypeId(Int32) },
        HirParam { name: "b", type_id: TypeId(Int32) },
    ],
    return_type: TypeId(Int32),
    body: HirExpr::BinOp(
        op: Add,
        lhs: HirExpr::Var("a"),
        rhs: HirExpr::Var("b"),
    ),
}
```

### Phase 5: Type Inference

**Input**: HIR
**Output**: Fully-typed HIR
**Module**: `simple/compiler/type_infer.spl`

Infers types using Hindley-Milner algorithm with extensions:
- **Unification**: Solves type equations
- **Generalization**: Introduces type variables
- **Trait constraints**: `where T: Trait` bounds
- **Effect inference**: Infers I/O and mutation effects

**Type Variables**:
```simple
fn identity(x):   // Type: ∀T. T → T
    x
```

### Phase 6: Monomorphization

**Input**: HIR with generics
**Output**: Specialized HIR (concrete types only)
**Module**: `simple/compiler/monomorphize/`

Specializes generic functions/types for each concrete type combination:

**Generic Template**:
```simple
fn identity<T>(x: T) -> T:
    x
```

**Call Sites**:
```simple
identity(42)      // Generates identity$Int
identity(3.14)    // Generates identity$Float
```

**Specialized Output**:
```rust
// identity$Int
fn identity_Int(x: Int) -> Int { x }

// identity$Float
fn identity_Float(x: Float) -> Float { x }
```

**Key Files**:
- `monomorphize/engine.rs` - Main monomorphization engine
- `monomorphize/metadata.rs` - Specialization tracking
- `monomorphize/partition.rs` - Template/specialized separation
- `monomorphize/deferred.rs` - On-demand instantiation (see below)

#### Generic Template Storage (New Feature)

As of v1.0, the compiler supports storing generic templates in .smf files for deferred monomorphization. This enables library-style generic imports where downstream code can instantiate new type combinations.

**Template Storage Pipeline**:

```
┌─────────────────────────────────────────────────────────────┐
│                    Monomorphization                          │
└─────────────────────────────────────────────────────────────┘
                              │
                              ↓
                    ┌──────────────────┐
                    │   Partitioning   │
                    └──────────────────┘
                              │
            ┌─────────────────┴─────────────────┐
            ↓                                   ↓
┌──────────────────────┐              ┌──────────────────────┐
│  Generic Templates   │              │ Specialized Instances│
│ - identity<T>        │              │ - identity$Int       │
│ - List<T>           │              │ - identity$Float     │
└──────────────────────┘              └──────────────────────┘
            │                                   │
            └──────────┬────────────────────────┘
                       ↓
            ┌──────────────────────┐
            │   SMF Writer         │
            ├──────────────────────┤
            │ Code Section         │ ← Specialized code
            │ TemplateCode Section │ ← Generic templates
            │ TemplateMeta Section │ ← Metadata
            └──────────────────────┘
```

**Deferred Instantiation**:

When a downstream module needs a new type combination:

1. **Load Templates**: Extract generic definitions from TemplateCode section
2. **Instantiate**: Generate specialized version with concrete type arguments
3. **Cache**: Store specialization to avoid redundant work
4. **Compile**: Lower to MIR and generate native code

**Two Modes**:
- **Link-Time**: Batch instantiate all needed specializations during linking
- **JIT-Time**: Lazy instantiate on first use during execution

**Example**:

```simple
# Library (collections.smf)
struct List<T>:
    data: [T]
    fn append(item: T): ...

# Compiled with List<Int>
val my_list = List<Int>()

# Downstream (app.spl)
import collections.List

fn main():
    # This works even though library didn't compile List<Float>!
    val floats = List<Float>()
    floats.append(3.14)
```

**Implementation Details**:
- `partition_generic_constructs()`: Separates templates from specializations
- `DeferredMonomorphizer`: On-demand instantiation engine
- `generate_smf_with_templates()`: Writes template sections to .smf

**See Also**: `doc/design/generic_template_bytecode.md` for full design document

### Phase 7: MIR Lowering

**Input**: Monomorphized HIR
**Output**: Mid-level Intermediate Representation (MIR)
**Module**: `simple/compiler/mir.spl`

Lowers HIR to a simpler, more explicit IR suitable for code generation:
- **SSA form**: Single Static Assignment for optimization
- **Explicit control flow**: Basic blocks and jumps
- **Explicit memory operations**: Load/store instructions
- **Type erasure**: Generic types fully specialized

**MIR Example**:
```simple
// Source
fn add(a: i32, b: i32) -> i32:
    a + b

// MIR
MirFunction {
    name: "add",
    blocks: [
        MirBlock {
            label: "entry",
            instructions: [
                %0 = LoadLocal(a)
                %1 = LoadLocal(b)
                %2 = IAdd(%0, %1)
                Return(%2)
            ]
        }
    ]
}
```

**MIR Instructions** (50+ instructions):
- **Arithmetic**: `IAdd`, `ISub`, `IMul`, `IDiv`, `FAdd`, `FSub`, ...
- **Control Flow**: `Jump`, `BranchIf`, `Return`, `Call`
- **Memory**: `LoadLocal`, `StoreLocal`, `LoadField`, `StoreField`
- **Type Operations**: `Cast`, `CheckType`, `UnwrapOption`

### Phase 8: Code Generation

**Input**: MIR
**Output**: Native code or bytecode
**Module**: `simple/compiler/codegen.spl`

Two backends:

#### Interpreter Backend

Tree-walking interpreter for MIR:
- **Direct execution**: No compilation overhead
- **Fast iteration**: Ideal for development/REPL
- **Full debugging**: Source-level debugging support

#### Cranelift Backend

JIT/AOT compiler to native code:
- **Cranelift IR**: Translates MIR → Cranelift IR
- **Optimization**: LICM, GVN, constant folding
- **Native code**: x86_64, ARM64, RISC-V targets

**Code Generation Pipeline**:
```
MIR → Cranelift IR → Machine Code → Object File
```

**Example**:
```
// MIR
%0 = IAdd(5, 3)

// Cranelift IR
v0 = iconst.i32 5
v1 = iconst.i32 3
v2 = iadd v0, v1

// x86_64 Assembly
mov eax, 5
add eax, 3
```

### Phase 9: SMF Writing

**Input**: Object code + templates (optional)
**Output**: Simple Module Format (.smf) file
**Module**: `simple/compiler/smf_writer.rs`

Packages compiled code into .smf binary format:

**SMF Structure**:
```
┌──────────────────────────────────────┐
│           SMF Header                 │
│  - magic: "SMF\0"                   │
│  - version: 0.1                     │
│  - platform: Linux/Windows/macOS    │
│  - arch: x86_64/aarch64             │
│  - section_count                    │
│  - symbol_count                     │
└──────────────────────────────────────┘
┌──────────────────────────────────────┐
│         Section Table                │
│  - Code section                     │
│  - Data section                     │
│  - TemplateCode section (optional)  │
│  - TemplateMeta section (optional)  │
└──────────────────────────────────────┘
┌──────────────────────────────────────┐
│         Code Section                 │
│  [native machine code]              │
└──────────────────────────────────────┘
┌──────────────────────────────────────┐
│      TemplateCode Section            │
│  [serialized generic templates]     │
└──────────────────────────────────────┘
┌──────────────────────────────────────┐
│      TemplateMeta Section            │
│  [monomorphization metadata]        │
└──────────────────────────────────────┘
┌──────────────────────────────────────┐
│         Symbol Table                 │
│  - function names + addresses       │
│  - template markers                 │
└──────────────────────────────────────┘
```

**Symbol Table**:
```rust
pub struct SmfSymbol {
    pub name_offset: u32,
    pub name_hash: u64,
    pub sym_type: SymbolType,      // Function/Data/Template
    pub binding: SymbolBinding,    // Local/Global/Weak
    pub value: u64,                // Address or offset
    pub size: u64,
    pub template_param_count: u8,  // For generic templates
    pub template_offset: u64,      // Offset to template definition
}
```

---

## Key Components

### Module Resolver

**File**: `src/rust/compiler/src/module_resolver/`

Resolves module imports and manages the module graph:
- **Path resolution**: Finds modules by name
- **Cycle detection**: Prevents circular imports
- **Dependency ordering**: Topologically sorts modules

**Example**:
```simple
import std.collections.List
import my_lib.utils
```

### Symbol Table

**File**: `src/rust/compiler/src/hir/lower/symbols.rs`

Tracks identifiers and their scopes:
- **Scope nesting**: Function → Module → Global
- **Name shadowing**: Inner scopes can shadow outer
- **Symbol lookup**: Efficient name resolution

### Type Registry

**File**: `src/rust/compiler/src/hir/type_registry.rs`

Central registry for all types in the program:
- **Type interning**: Each type has unique TypeId
- **Trait resolution**: Tracks impl blocks
- **Type queries**: Check subtyping, equality

### Effect System

**File**: `src/rust/compiler/src/hir/effects.rs`

Tracks computational effects:
- **I/O**: File, network, console operations
- **Mutation**: Mutable variable access
- **Async**: Asynchronous operations
- **Non-determinism**: Random, time-based

---

## Intermediate Representations

### AST (Abstract Syntax Tree)

**Characteristics**:
- **High-level**: Close to source code structure
- **Untyped**: No type information yet
- **Generic-aware**: Preserves generic parameters

**Key Types**:
```simple
struct FunctionDef:
    name: text
    generic_params: [text]
    params: [Param]
    return_type: Type?
    body: Expr
    is_generic_template: bool
```

### HIR (High-level IR)

**Characteristics**:
- **Typed**: All expressions have types
- **Resolved**: Names bound to definitions
- **Generic**: Still contains type parameters

**Key Types**:
```simple
struct HirFunction:
    name: text
    params: [HirParam]
    return_type: TypeId
    body: HirExpr
    effects: [Effect]
```

### MIR (Mid-level IR)

**Characteristics**:
- **Monomorphized**: No generics
- **SSA form**: Single Static Assignment
- **Explicit control flow**: Basic blocks
- **Simple instructions**: ~50 instruction types

**Key Types**:
```simple
struct MirFunction:
    name: text
    params: [MirLocal]
    return_type: TypeId
    blocks: [MirBlock]
    generic_params: [text]         # For templates
    is_generic_template: bool       # Template marker
```

---

## Type System

### Type Hierarchy

```
Type
├── Primitive
│   ├── Int (i8, i16, i32, i64)
│   ├── Float (f32, f64)
│   ├── Bool
│   └── String
├── Compound
│   ├── Tuple (T1, T2, ...)
│   ├── Array [T]
│   ├── Dict {K: V}
│   └── Function (T1, T2) -> T3
├── User-Defined
│   ├── Struct
│   ├── Class
│   ├── Enum
│   └── Trait
└── Generic
    ├── TypeVar (unbound)
    └── Generic<T> (parameterized)
```

### Generic Types

**Syntax**:
```simple
fn identity<T>(x: T) -> T:
    x

struct List<T>:
    data: [T]

enum Result<T, E>:
    Ok(T)
    Err(E)
```

**Constraints**:
```simple
fn sort<T>(items: [T]) where T: Comparable<T>:
    # T must implement Comparable
```

### Type Inference

**Algorithm**: Hindley-Milner with extensions

**Unification**:
```
identity(42)
→ T = Int  (unify with Int literal)
→ identity : Int → Int
```

**Generalization**:
```
fn identity(x):
    x
→ identity : ∀T. T → T
```

---

## Monomorphization

### Overview

Monomorphization converts generic code into specialized versions for each concrete type combination used in the program.

**Example**:
```simple
fn max<T>(a: T, b: T) -> T where T: Comparable<T>:
    if a > b: a else: b

val x = max(5, 10)         # Generates max$Int
val y = max(3.14, 2.71)    # Generates max$Float
```

### Specialization

**Name Mangling**:
```
identity<T>          → identity_T (template)
identity<Int>        → identity$Int
identity<Float>      → identity$Float
List<Result<Int, E>> → List$Result$Int$E
```

**Specialization Table**:
```rust
HashMap<SpecializationKey, CompiledCode>

SpecializationKey {
    name: "identity",
    type_args: [Int],
}
→ CompiledCode::Function(identity$Int)
```

### Deferred Monomorphization

**Problem**: Pre-compiling all type combinations is impossible

**Solution**: Store templates in .smf, instantiate on-demand

**Workflow**:
1. Compile library with templates + common specializations
2. Downstream code references new type combination
3. Linker/JIT detects missing specialization
4. DeferredMonomorphizer instantiates from template
5. New specialization compiled and linked

**See**: `doc/design/generic_template_bytecode.md`

---

## Code Generation

### Cranelift Integration

**Cranelift IR**:
```
function %add(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    v2 = iadd v0, v1
    return v2
}
```

**Translation**:
- MIR instructions → Cranelift instructions
- Type mapping (i32 → Cranelift i32)
- Function calls via symbol table

### Optimization

**Cranelift Passes**:
- **LICM**: Loop-Invariant Code Motion
- **GVN**: Global Value Numbering
- **DCE**: Dead Code Elimination
- **Constant Folding**: Evaluate constants
- **Inlining**: Small function inlining

**Optimization Levels**:
- **Minimal**: Fast compilation (current default for templates)
- **Standard**: Balanced compilation/runtime
- **Aggressive**: Slow compilation, fast runtime

---

## Module System

### Module Structure

```simple
# my_module.spl
export List, sort

struct List<T>:
    data: [T]

fn sort<T>(items: [T]) -> [T]:
    # ...
```

### Import Resolution

**Search Path**:
1. Current directory
2. `src/lib/std/` (standard library)
3. `~/.simple/packages/` (user packages)
4. Environment variable `SIMPLE_PATH`

**Import Forms**:
```simple
import std.collections.List        # Specific item
import std.collections.*           # All exports
import my_lib.utils as U           # Alias
```

### Linking

**Static Linking**:
```bash
simple compile lib.spl -o lib.smf
simple compile app.spl --link lib.smf -o app
```

**Dynamic Linking** (future):
```bash
simple compile lib.spl -o lib.so --shared
simple compile app.spl -L. -llib -o app
```

---

## Implementation Notes

### Self-Hosting

The Simple compiler is implemented in both Rust (`simple_old`) and Simple (`simple_new`):

**Bootstrap Process**:
1. Rust compiler compiles Simple compiler source
2. Simple compiler (running on Rust runtime) compiles itself
3. Self-compiled version validates against Rust version

**File Locations**:
- Rust implementation: `src/rust/compiler/`
- Simple implementation: `simple/compiler/`

### Testing Strategy

**Test Levels**:
1. **Unit Tests**: Per-module tests (Rust `cargo test`)
2. **Integration Tests**: Cross-module tests
3. **System Tests**: End-to-end compilation
4. **SSpec Tests**: Feature specifications (BDD)

**Coverage**:
- Lexer: 95%
- Parser: 92%
- HIR: 88%
- MIR: 85%
- Codegen: 78%

---

## References

### Related Documents

- **Type System**: `doc/design/type_system.md`
- **Monomorphization**: `doc/design/monomorphization.md`
- **Generic Template Bytecode**: `doc/design/generic_template_bytecode.md` ← **New!**
- **SMF Format Specification**: `doc/format/smf_specification.md` ← **New!**
- **Effect System**: `doc/design/effects.md`

### Source Code

**Rust Compiler**:
- Pipeline: `src/rust/compiler/src/pipeline/`
- HIR: `src/rust/compiler/src/hir/`
- MIR: `src/rust/compiler/src/mir/`
- Codegen: `src/rust/compiler/src/codegen/`
- Monomorphization: `src/rust/compiler/src/monomorphize/`

**Simple Compiler**:
- Pipeline: `simple/compiler/driver.spl`
- HIR: `simple/compiler/hir.spl`
- MIR: `simple/compiler/mir.spl`
- Codegen: `simple/compiler/codegen.spl`
- Monomorphization: `simple/compiler/monomorphize/`

---

**Last Updated**: 2026-01-28
**Contributors**: Simple Language Team
