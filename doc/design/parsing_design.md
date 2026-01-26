# Parsing Architecture Design

## Overview

This document describes the parsing architecture for the Simple language compiler and interpreter. The architecture uses a unified frontend with TreeSitter, supporting both code (`.spl`) and config/data (`.sdn`) files through the same pipeline.

## Architecture Diagram

```
          ┌─────────────────────────────────────────────────────────┐
          │                      INPUT                              │
          │                                                         │
          │    ┌──────────────┐         ┌──────────────┐           │
          │    │    Config    │         │    Code      │           │
          │    │   (*.sdn)    │         │   (*.spl)    │           │
          │    └──────┬───────┘         └──────┬───────┘           │
          │           └────────────┬───────────┘                   │
          └────────────────────────┼───────────────────────────────┘
                                   │
                                   ▼
          ┌─────────────────────────────────────────────────────────┐
          │                   FRONTEND (Parsing)                    │
          │                                                         │
          │                 ┌─────────────┐                        │
          │                 │ TreeSitter  │                        │
          │                 │ (Frontend)  │                        │
          │                 └──────┬──────┘                        │
          │                        │                               │
          │                        ▼                               │
          │                 ┌─────────────┐                        │
          │                 │Custom Blocks│                        │
          │                 │m{} sh{} sql{}                        │
          │                 │re{} md{} ...│                        │
          │                 └──────┬──────┘                        │
          │                        │                               │
          │                        ▼                               │
          │                 ┌─────────────┐                        │
          │                 │   Lexer     │                        │
          │                 └──────┬──────┘                        │
          │                        │                               │
          │                        ▼                               │
          │                 ┌─────────────┐                        │
          │                 │   Parser    │                        │
          │                 │   (AST)     │                        │
          │                 └──────┬──────┘                        │
          └────────────────────────┼────────────────────────────────┘
                                   │
                    ┌──────────────┴──────────────┐
                    │                             │
                    ▼                             ▼
          ┌─────────────────┐          ┌─────────────────┐
          │   SDN Capture   │          │   Code Path     │
          │   (write AST)   │          │                 │
          │                 │          │        ▼        │
          │ skip contracts  │          │ ┌─────────────┐ │
          │ skip constraints│          │ │  HIR Layer  │ │
          │                 │          │ │ Constraints │ │
          └─────────────────┘          │ │ Contracts   │ │
                                       │ │  (shared)   │ │
                                       │ └──────┬──────┘ │
                                       │        ▼        │
                                       │ ┌─────────────┐ │
                                       │ │     MIR     │ │
                                       │ │ (shared IR) │ │
                                       │ └──────┬──────┘ │
                                       └────────┼────────┘
                                                │
                                 ┌──────────────┴──────────────┐
                                 │                             │
                                 ▼                             ▼
                       ┌─────────────────┐          ┌─────────────────┐
                       │   Interpreter   │          │    Compiler     │
                       │   (MIR eval)    │          │  Cranelift/LLVM │
                       └────────┬────────┘          └────────┬────────┘
                                │                            │
                                └──────────────┬─────────────┘
                                               │
                                               ▼
                                 ┌─────────────────────────────┐
                                 │     Shared FFI Interface    │
                                 └──────────────┬──────────────┘
                                                │
                                                ▼
                                 ┌─────────────────────────────┐
                                 │          Runtime            │
                                 │     (GC, Value, Memory)     │
                                 └─────────────────────────────┘
```

## Frontend Components

### 1. TreeSitter (Parser Frontend)

TreeSitter provides the primary parsing frontend with:
- Incremental parsing for IDE integration
- Error recovery for partial/incomplete code
- Syntax highlighting queries
- Language detection

**Location:** `src/lib/std/src/parser/treesitter/`

```
treesitter/
├── __init__.spl           # Module exports
├── lexer.spl              # Lexer wrapper
├── parser.spl             # Parser wrapper
├── tree.spl               # Tree/Node types
├── query.spl              # Query API
├── edits.spl              # Incremental editing
├── error_recovery.spl     # Error recovery
├── language_detect.spl    # Language detection
├── grammar/               # Grammar definitions
└── queries/               # Predefined queries
```

### 2. Custom Blocks

Custom blocks provide DSL embedding within Simple code. Blocks are parsed before standard lexer tokenization.

**Location:** `src/rust/compiler/src/blocks/`

| Block | Syntax | Purpose |
|-------|--------|---------|
| `m{}` | `m{ sqrt(16) + pi * r^2 }` | Math expressions |
| `sh{}` | `sh{ ls -la \| grep .spl }` | Shell commands |
| `sql{}` | `sql{ SELECT * FROM users WHERE id = $1 }` | SQL queries |
| `re{}` | `re{ \d{3}-\d{4} }` | Regex patterns |
| `md{}` | `md{ # Heading }` | Markdown (planned) |
| `html{}` | `html{ <div>...</div> }` | HTML (planned) |
| `graph{}` | `graph{ A -> B }` | Diagrams (planned) |

**Custom Block Parsing Flow:**

```
Source Code
    │
    ▼
┌─────────────────────────────────────┐
│ 1. Scan for block markers           │
│    m{ sh{ sql{ re{ ...              │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 2. Extract block payload            │
│    - Match balanced braces          │
│    - Handle nested blocks           │
│    - Preserve raw content           │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 3. Parse block-specific syntax      │
│    - m{}: Math expression parser    │
│    - sh{}: Shell command parser     │
│    - sql{}: SQL statement parser    │
│    - re{}: Regex pattern parser     │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│ 4. Generate block AST node          │
│    - BlockExpr { kind, payload }    │
│    - Attach to main AST             │
└──────────────┬──────────────────────┘
               │
               ▼
    Continue to Lexer
```

### 3. Lexer

Tokenizes source code after custom block extraction.

**Location:** `src/rust/parser/src/lexer/`

### 4. Parser

Generates AST from token stream.

**Location:** `src/rust/parser/src/`

## Path Divergence: SDN vs Code

After parsing, the pipeline diverges based on input type:

### SDN Path (Config/Data)

SDN files (`.sdn`) are captured after parsing and written directly:

- **No contract validation**
- **No constraint checking**
- **No type inference**
- **Direct AST serialization**

Use cases:
- Configuration files (`simple.toml` equivalent)
- Test databases (`doc/test/test_db.sdn`)
- Feature databases (`doc/feature/feature_db.sdn`)
- TODO tracking (`doc/todo/todo_db.sdn`)

### Code Path

Code files (`.spl`) continue through the full pipeline:

1. **HIR Layer** - Constraints and contracts (shared)
2. **MIR Layer** - Mid-level IR (shared)
3. **Backend** - Interpreter or Compiler

## HIR Layer (Shared)

The HIR layer contains constraint and contract validation shared by both interpreter and compiler.

**Location:** `src/rust/compiler/src/hir/`

```
hir/
├── mod.rs              # HIR module root
├── lower.rs            # AST → HIR lowering
├── types.rs            # HIR type definitions
├── constraints.rs      # Constraint checking (shared)
├── contracts.rs        # Contract validation (shared)
└── visitor.rs          # HIR traversal
```

**Shared Components:**
- Dimension constraints (neural network layer checking)
- Type contracts (pre/post conditions)
- Effect tracking
- Borrow checking rules

## MIR Layer (Shared)

The MIR (Mid-level IR) is the shared representation used by both interpreter and compiler backends.

**Location:** `src/rust/compiler/src/mir/`

```
mir/
├── mod.rs              # MIR module root
├── inst_enum.rs        # MIR instruction definitions
├── inst_effects.rs     # Instruction side effects
├── inst_helpers.rs     # Instruction utilities
└── lower/              # HIR → MIR lowering
    ├── lowering_expr.rs
    └── lowering_stmt.rs
```

## Backend Layer

### Interpreter

Directly evaluates MIR instructions.

**Location:** `src/rust/compiler/src/interpreter*.rs`

### Compiler

Generates native code from MIR.

**Location:** `src/rust/compiler/src/codegen/`

| Backend | Status | Use Case |
|---------|--------|----------|
| Cranelift | Stable | JIT, fast compilation |
| LLVM | Supported | AOT, optimization |

## Shared FFI Interface

Both interpreter and compiler share the same FFI interface for runtime operations.

**Location:** `src/rust/runtime/src/value/`

```
value/
├── mod.rs              # FFI exports
├── cli_ffi.rs          # CLI operations
├── collections.rs      # Collection FFI
├── io_ffi.rs           # I/O operations
└── ...
```

**FFI Categories:**
- File system operations
- Network operations
- Process management
- Collection manipulation
- String operations
- Math operations

## Pipeline Summary

| Stage | SDN | Code | Shared |
|-------|-----|------|--------|
| Input | *.sdn | *.spl | - |
| TreeSitter | Yes | Yes | Yes |
| Custom Blocks | Yes | Yes | Yes |
| Lexer | Yes | Yes | Yes |
| Parser (AST) | Yes | Yes | Yes |
| **Capture/Write** | **Yes** | No | - |
| HIR (Constraints) | No | Yes | Yes |
| HIR (Contracts) | No | Yes | Yes |
| MIR | No | Yes | Yes |
| Interpreter | No | Yes | - |
| Compiler | No | Yes | - |
| FFI | No | Yes | Yes |
| Runtime | No | Yes | Yes |

## File Locations

| Component | Rust Location | Simple Location |
|-----------|---------------|-----------------|
| TreeSitter | - | `src/lib/std/src/parser/treesitter/` |
| Custom Blocks | `src/rust/compiler/src/blocks/` | `simple/compiler/blocks/` |
| Lexer | `src/rust/parser/src/lexer/` | `simple/compiler/lexer.spl` |
| Parser | `src/rust/parser/src/` | `simple/compiler/parser.spl` |
| SDN | `src/rust/sdn/` | `src/app/sdn/` |
| HIR | `src/rust/compiler/src/hir/` | `simple/compiler/hir.spl` |
| MIR | `src/rust/compiler/src/mir/` | `simple/compiler/mir.spl` |
| Codegen | `src/rust/compiler/src/codegen/` | `simple/compiler/codegen.spl` |
| FFI | `src/rust/runtime/src/value/` | - |
| Runtime | `src/rust/runtime/` | - |

## Self-Hosting Compiler

The self-hosting compiler (written in Simple) mirrors this architecture:

**Location:** `simple/compiler/`

```
simple/compiler/
├── __init__.spl           # Module root
├── driver.spl             # Compilation driver
├── treesitter.spl         # TreeSitter integration
├── blocks/                # Custom block handlers
│   └── resolver.spl
├── lexer.spl              # Lexer
├── parser.spl             # Parser
├── hir.spl                # HIR (with constraints/contracts)
├── mir.spl                # MIR
├── codegen.spl            # Code generation
├── resolve.spl            # Name resolution
├── type_infer.spl         # Type inference
├── dim_constraints.spl    # Dimension checking
├── aop.spl                # AOP support
├── di.spl                 # Dependency injection
└── config.spl             # Compiler config
```

## References

- Custom Block Design: `doc/design/custom_block_implementation_plan.md`
- TreeSitter Guide: `doc/guide/treesitter_integration_guide.md`
- SDN Format: `src/rust/sdn/`
- HIR Core Types: `src/rust/hir-core/`
