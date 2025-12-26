# Ahead of Time Compilation Plan

This document describes the AOT compilation plan for the Simple Language Compiler.

## Index

| File | Content |
|------|---------|
| [05_ahead_of_time_compile.md](05_ahead_of_time_compile.md) | Overview, Architecture, HIR Types |
| [05_ahead_of_time_compile_lowering.md](05_ahead_of_time_compile_lowering.md) | AST to HIR, MIR Types |
| [05_ahead_of_time_compile_codegen.md](05_ahead_of_time_compile_codegen.md) | HIR to MIR, Cranelift Backend |
| [05_ahead_of_time_compile_smf.md](05_ahead_of_time_compile_smf.md) | SMF Linker, Pipeline, Summary |

---


## Overview

Implement AOT compilation for Simple language that compiles source to native code (.smf files) before execution. This enables interpreter-like workflow: edit -> run (compile happens automatically if source changed).

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                     AOT Compilation Pipeline                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐       │
│  │  Source  │───▶│  Parser  │───▶│   HIR    │───▶│   MIR    │       │
│  │  .simple │    │  (AST)   │    │(High IR) │    │ (Mid IR) │       │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘       │
│                                                        │             │
│                                                        ▼             │
│                                         ┌──────────────────────┐    │
│                                         │    Code Generator    │    │
│                                         │  ┌────────────────┐  │    │
│                                         │  │   Cranelift    │  │    │
│                                         │  │   (or LLVM)    │  │    │
│                                         │  └────────────────┘  │    │
│                                         └──────────┬───────────┘    │
│                                                    │                 │
│                                                    ▼                 │
│  ┌──────────┐    ┌──────────┐    ┌──────────────────────────┐       │
│  │  Output  │◀───│  Linker  │◀───│    Native Code (.o)      │       │
│  │   .smf   │    │  (SMF)   │    │                          │       │
│  └──────────┘    └──────────┘    └──────────────────────────┘       │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
crates/compiler/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── pipeline.rs         # Main compilation pipeline
    ├── hir/
    │   ├── mod.rs          # High-level IR
    │   ├── lower.rs        # AST -> HIR
    │   └── types.rs        # HIR types
    ├── mir/
    │   ├── mod.rs          # Mid-level IR
    │   ├── lower.rs        # HIR -> MIR
    │   ├── optimize.rs     # MIR optimizations
    │   └── types.rs        # MIR types
    ├── codegen/
    │   ├── mod.rs          # Code generation
    │   ├── cranelift.rs    # Cranelift backend
    │   └── abi.rs          # Calling conventions
    ├── linker/
    │   ├── mod.rs          # SMF linker
    │   └── emit.rs         # SMF file emission
    └── cache/
        ├── mod.rs          # Compilation cache
        └── incremental.rs  # Incremental compilation
```

---

## High-Level IR (HIR)

### HIR Types (hir/types.rs)

```rust
// crates/compiler/src/hir/types.rs

use std::collections::HashMap;

/// Module after type checking
#[derive(Debug)]
pub struct HirModule {
    pub name: String,
    pub source_hash: u64,
    pub items: Vec<HirItem>,
    pub types: TypeTable,
}

#[derive(Debug)]
pub enum HirItem {
    Function(HirFunction),
    Struct(HirStruct),
    Enum(HirEnum),
    Trait(HirTrait),
    Impl(HirImpl),
    Actor(HirActor),
    Constant(HirConstant),
}

#[derive(Debug)]
pub struct HirFunction {
    pub name: String,
    pub params: Vec<HirParam>,
    pub return_type: TypeId,
    pub body: HirBlock,
    pub is_public: bool,
    pub effect: Effect,
}

#[derive(Debug, Clone, Copy)]
pub enum Effect {
    None,
    Async,
    Async,
}

#[derive(Debug)]
pub struct HirParam {
    pub name: String,
    pub ty: TypeId,
    pub is_mutable: bool,
}

#[derive(Debug)]
pub struct HirBlock {
    pub stmts: Vec<HirStmt>,
    pub expr: Option<Box<HirExpr>>,
}

#[derive(Debug)]
pub enum HirStmt {
    Let {
        name: String,
        ty: TypeId,
        init: Option<HirExpr>,
        is_mutable: bool,
    },
    Assign {
        target: HirExpr,
        value: HirExpr,
    },
    Expr(HirExpr),
    Return(Option<HirExpr>),
    Break(Option<String>),
    Continue(Option<String>),
}

#[derive(Debug)]
pub enum HirExpr {
    // Literals (with resolved types)
    IntLit(i64, TypeId),
    FloatLit(f64, TypeId),
    BoolLit(bool),
    StringLit(String),
    NilLit,

    // References
    Var(String, TypeId),
    Field {
        base: Box<HirExpr>,
        field: String,
        ty: TypeId,
    },
    Index {
        base: Box<HirExpr>,
        index: Box<HirExpr>,
        ty: TypeId,
    },

    // Operations
    Binary {
        op: BinOp,
        left: Box<HirExpr>,
        right: Box<HirExpr>,
        ty: TypeId,
    },
    Unary {
        op: UnaryOp,
        operand: Box<HirExpr>,
        ty: TypeId,
    },
    Call {
        func: Box<HirExpr>,
        args: Vec<HirExpr>,
        ty: TypeId,
    },
    MethodCall {
        receiver: Box<HirExpr>,
        method: String,
        args: Vec<HirExpr>,
        ty: TypeId,
    },

    // Control flow
    If {
        condition: Box<HirExpr>,
        then_branch: HirBlock,
        else_branch: Option<HirBlock>,
        ty: TypeId,
    },
    Match {
        subject: Box<HirExpr>,
        arms: Vec<HirMatchArm>,
        ty: TypeId,
    },
    Loop {
        label: Option<String>,
        body: HirBlock,
    },

    // Constructors
    Struct {
        name: String,
        fields: Vec<(String, HirExpr)>,
        ty: TypeId,
    },
    Tuple(Vec<HirExpr>, TypeId),
    Array(Vec<HirExpr>, TypeId),

    // Memory
    New {
        kind: PointerKind,
        ty: TypeId,
        args: Vec<HirExpr>,
    },
    Borrow {
        mutable: bool,
        expr: Box<HirExpr>,
        ty: TypeId,
    },
    Deref {
        expr: Box<HirExpr>,
        ty: TypeId,
    },

    // Concurrency
    Spawn {
        expr: Box<HirExpr>,
        ty: TypeId,
    },
    Send {
        target: Box<HirExpr>,
        message: Box<HirExpr>,
    },

    // Lambda
    Lambda {
        params: Vec<HirParam>,
        body: HirBlock,
        captures: Vec<String>,
        ty: TypeId,
    },

    // Type cast
    Cast {
        expr: Box<HirExpr>,
        target_ty: TypeId,
    },
}

/// Type ID for efficient type comparison
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// Type table for interned types
pub struct TypeTable {
    types: Vec<Type>,
    intern_map: HashMap<Type, TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    // Primitives
    Int,
    Float,
    Bool,
    Char,
    String,
    Nil,

    // Compound
    Tuple(Vec<TypeId>),
    Array(TypeId, Option<usize>),
    Function { params: Vec<TypeId>, ret: TypeId },

    // User-defined
    Struct(String),
    Enum(String),
    Trait(String),
    Actor(String),

    // Pointers
    Pointer(PointerKind, TypeId),
    Borrow { mutable: bool, inner: TypeId },

    // Type variable (for generics)
    TypeVar(u32),
}
```

---

Next: [AST to HIR Lowering](05_ahead_of_time_compile_lowering.md)
