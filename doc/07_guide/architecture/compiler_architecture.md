# Compiler Architecture

The Simple compiler is a multi-stage compiler that transforms `.spl` source code into native executables or bytecode modules (.smf files).

---

## Compilation Modes

- **Interpret**: Tree-walking interpreter for rapid development
- **JIT**: Just-In-Time compilation for interactive execution
- **AOT**: Ahead-Of-Time compilation to native binaries
- **Check**: Type checking only (no code generation)

---

## Pipeline Overview

```
Source Code (.spl)
    |
    v
Lexer              -> Token stream
    |
    v
Parser             -> AST (Abstract Syntax Tree)
    |
    v
Block Resolver     -> Custom blocks expanded
    |
    v
HIR Lowering       -> High-level IR (typed, resolved names)
    |
    v
Type Inference     -> Fully-typed HIR (Hindley-Milner)
    |
    v
Monomorphizer      -> Generic specialization
    |
    v
MIR Lowering       -> Mid-level IR (SSA, explicit control flow)
    |
    v
Code Generation    -> Interpreter / Cranelift / LLVM
    |
    v
SMF Writer         -> .smf/.o/.exe output
```

---

## Key Phases

### Lexical Analysis

Produces token stream from source. Handles indentation-based blocks, string interpolation (`"Hello {name}"`), math blocks (`m{...}`), and error recovery.

### Parsing

Recursive descent parser producing AST. Supports operator precedence climbing, pattern matching with exhaustiveness checking, and generics (`<>` syntax).

### HIR Lowering

Transforms AST into typed intermediate form with name resolution, scope tracking, trait resolution, and effect tracking (I/O, mutation, async).

### Type Inference

Hindley-Milner algorithm with extensions: unification, generalization, trait constraints (`where T: Trait`), and effect inference.

### Monomorphization

Specializes generic functions/types for each concrete type combination:

```simple
fn identity<T>(x: T) -> T: x

identity(42)    # Generates identity$Int
identity(3.14)  # Generates identity$Float
```

Generic templates can be stored in .smf files for deferred monomorphization, enabling library-style generic imports.

### MIR Lowering

Lowers HIR to SSA form with explicit control flow (basic blocks and jumps), explicit memory operations, and ~50 instruction types.

### Code Generation

**Interpreter backend:** Direct tree-walking execution, ideal for development/REPL.

**Cranelift backend:** JIT/AOT compilation to native code (x86_64, ARM64, RISC-V). Optimizations include LICM, GVN, DCE, constant folding, and inlining.

---

## SMF Format

Simple Module Format (.smf) packages compiled code:

```
SMF Header    (magic, version, platform, arch)
Section Table (Code, Data, TemplateCode, TemplateMeta)
Code Section  (native machine code)
Template Sections (serialized generic templates + metadata)
Symbol Table  (function names, addresses, template markers)
```

---

## Type System

```
Type
  Primitive: Int (i8-i64), Float (f32/f64), Bool, String
  Compound:  Tuple, Array, Dict, Function
  User:      Struct, Class, Enum, Trait
  Generic:   TypeVar, Generic<T>
```

Constraints: `fn sort<T>(items: [T]) where T: Comparable<T>`

---

## Module System

**Import resolution search path:**

1. Current directory
2. `src/lib/std/` (standard library)
3. `~/.simple/packages/` (user packages)
4. `SIMPLE_PATH` environment variable

**Import forms:**

```simple
use std.collections.List        # Specific item
use std.collections.*           # All exports
use my_lib.utils as U           # Alias
```

**Linking:**

```bash
simple compile lib.spl -o lib.smf
simple compile app.spl --link lib.smf -o app
```

---

## Source Code Layout

The compiler source is organized by numbered pipeline layers in `src/compiler/`:

| Layer | Directory | Role |
|-------|-----------|------|
| 00 | common/ | Error types, config, diagnostics |
| 10 | frontend/ | Lexer, parser, AST, desugar |
| 15 | blocks/ | Block definition system |
| 20 | hir/ | HIR types, definitions, lowering |
| 25 | traits/ | Trait solver, coherence |
| 30 | types/ | Type inference, type system |
| 35 | semantics/ | Semantic analysis, lint |
| 40 | mono/ | Monomorphization |
| 50 | mir/ | MIR types, lowering |
| 55 | borrow/ | Borrow checking |
| 60 | mir_opt/ | MIR optimization passes |
| 70 | backend/ | Code generation backends |
| 80 | driver/ | Driver, pipeline, build |
| 90 | tools/ | API, coverage, symbols |
| 95 | interp/ | Interpreter |
| 99 | loader/ | Module resolver |

---

## Related Files

- Application architecture: `doc/07_guide/architecture/application_architecture.md`
- Type system design: `doc/05_design/type_system.md`
- Generic template bytecode: `doc/05_design/generic_template_bytecode.md`
- SMF format spec: `doc/format/smf_specification.md`
