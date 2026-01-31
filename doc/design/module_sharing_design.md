# Module Sharing Design

## Overview

This document describes the target architecture where **most logic is implemented in Simple**, with Rust providing only bootstrapping and low-level FFI bindings.

**Key Insight**: Since Simple compiles to LLVM/Cranelift native code, it runs at the same speed as Rust. Therefore, we should maximize Simple code and minimize Rust code.

---

## Design Principle

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SIMPLE = RUST SPEED                             │
│                                                                         │
│   Simple Code  ──compile──►  LLVM/Cranelift  ──►  Native Code          │
│   Rust Code    ──compile──►  LLVM            ──►  Native Code          │
│                                                                         │
│   Both produce similar machine code. No performance reason to use Rust. │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Core Architecture: Lexer → TreeSitter → Parser

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         PARSING PIPELINE                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Source Code (.spl)                                                    │
│         │                                                               │
│         ▼                                                               │
│   ┌─────────────┐                                                       │
│   │   LEXER     │  Tokenize source into token stream                   │
│   │  lexer.spl  │  Output: [Token(kind, span, value), ...]             │
│   └──────┬──────┘                                                       │
│          │                                                              │
│          ▼                                                              │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                      TREESITTER                                  │  │
│   │                    treesitter.spl                                │  │
│   │                                                                  │  │
│   │  • High-level structure parsing (outline mode)                   │  │
│   │  • Error recovery (partial parsing)                              │  │
│   │  • Incremental parsing (for IDE)                                 │  │
│   │  • Syntax highlighting ranges                                    │  │
│   │                                                                  │  │
│   │  Output: OutlineAST (functions, classes, imports - no bodies)   │  │
│   └──────────────────────────┬──────────────────────────────────────┘  │
│                              │                                          │
│                              ▼                                          │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                        PARSER                                    │  │
│   │                      parser.spl                                  │  │
│   │                                                                  │  │
│   │  • Uses TreeSitter outline as skeleton                          │  │
│   │  • Fills in function bodies, expressions                        │  │
│   │  • Full AST construction                                        │  │
│   │  • Type annotations                                             │  │
│   │                                                                  │  │
│   │  Output: Full AST                                               │  │
│   └──────────────────────────┬──────────────────────────────────────┘  │
│                              │                                          │
│                              ▼                                          │
│                         Full AST                                        │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Configuration & Dependency Injection

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    CONFIG + DI + AOP SETUP                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                      config.spl                                    │ │
│  │  • Load configuration from .sdn files                             │ │
│  │  • Environment variables                                          │ │
│  │  • Command-line arguments                                         │ │
│  │  • Profile selection (dev, test, prod, sdn)                       │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                              │                                          │
│                              ▼                                          │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                        di.spl                                      │ │
│  │  • Dependency injection container                                 │ │
│  │  • Service registration and resolution                            │ │
│  │  • Profile-based bindings                                         │ │
│  │                                                                   │ │
│  │  Profiles:                                                        │ │
│  │    dev  → FullHirInst, DebugLogger                               │ │
│  │    prod → FullHirInst, ProductionLogger                          │ │
│  │    test → FullHirInst, TestLogger                                │ │
│  │    sdn  → SdnHirInst (no-op), SdnLogger                          │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                              │                                          │
│                              ▼                                          │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                        aop.spl                                     │ │
│  │  • Aspect-oriented programming for cross-cutting concerns         │ │
│  │  • Logging aspect (wraps functions with log calls)                │ │
│  │  • Tracing aspect (performance monitoring)                        │ │
│  │  • Error handling aspect                                          │ │
│  │                                                                   │ │
│  │  Example:                                                         │ │
│  │    @log(level: DEBUG)                                             │ │
│  │    fn parse_expr() -> Expr:                                       │ │
│  │        ...                                                        │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## HIR Architecture: Shared HIR → Different Backends

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         HIR LAYER (SHARED)                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                        hir.spl (SHARED)                            │ │
│  │                                                                   │ │
│  │  Same HIR used by ALL modes:                                      │ │
│  │  • HirModule, HirFunction, HirBlock                               │ │
│  │  • HirExpr, HirStmt, HirPattern                                   │ │
│  │  • TypeInfo, FunctionSignature                                    │ │
│  │  • SymbolTable, ScopeInfo                                         │ │
│  │  • StructLayout, EnumLayout                                       │ │
│  │                                                                   │ │
│  │  HIR Operations (abstract interface):                             │ │
│  │  • visit_function(fn) → Backend                                   │ │
│  │  • visit_expr(expr) → Backend                                     │ │
│  │  • visit_stmt(stmt) → Backend                                     │ │
│  │                                                                   │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                              │                                          │
│                              │  HIR connects to different backends      │
│                              │  via Backend trait (DI injected)         │
│                              │                                          │
│         ┌────────────────────┼────────────────────┐                    │
│         │                    │                    │                    │
│         ▼                    ▼                    ▼                    │
│  ┌─────────────┐      ┌─────────────┐      ┌─────────────┐            │
│  │  COMPILER   │      │ INTERPRETER │      │     SDN     │            │
│  │  BACKEND    │      │   BACKEND   │      │   BACKEND   │            │
│  │             │      │             │      │   (NO-OP)   │            │
│  │ mir.spl     │      │ eval.spl    │      │ sdn_back.spl│            │
│  │             │      │             │      │             │            │
│  │ HIR → MIR   │      │ HIR → Value │      │ HIR → Data  │            │
│  │ lowering    │      │ execution   │      │ only        │            │
│  └──────┬──────┘      └──────┬──────┘      └──────┬──────┘            │
│         │                    │                    │                    │
│         ▼                    ▼                    ▼                    │
│  ┌─────────────┐      ┌─────────────┐      ┌─────────────┐            │
│  │ codegen.spl │      │  Runtime    │      │  SdnValue   │            │
│  │             │      │  Value      │      │  (data only)│            │
│  │ MIR → Native│      │             │      │             │            │
│  └──────┬──────┘      └─────────────┘      └─────────────┘            │
│         │                                                              │
│         ▼                                                              │
│   Cranelift/LLVM                                                       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Backend Trait (DI Interface)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         BACKEND TRAIT                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  # hir.spl - Abstract backend interface                                 │
│  trait Backend:                                                         │
│      fn visit_function(hir_fn: HirFunction) -> Result                  │
│      fn visit_expr(expr: HirExpr) -> Result                            │
│      fn visit_stmt(stmt: HirStmt) -> Result                            │
│      fn visit_call(call: HirCall) -> Result                            │
│      fn visit_binary(op: BinOp, left: HirExpr, right: HirExpr) -> Res  │
│                                                                         │
│  ─────────────────────────────────────────────────────────────────────  │
│                                                                         │
│  # compiler_backend.spl - Compiles to MIR                               │
│  class CompilerBackend(Backend):                                        │
│      mir_builder: MirBuilder                                           │
│                                                                         │
│      fn visit_expr(expr: HirExpr) -> MirValue:                         │
│          match expr:                                                    │
│              HirBinary(op, l, r) => self.mir_builder.emit_binop(op,l,r)│
│              HirCall(fn, args) => self.mir_builder.emit_call(fn, args) │
│              ...                                                        │
│                                                                         │
│  ─────────────────────────────────────────────────────────────────────  │
│                                                                         │
│  # interpreter_backend.spl - Executes directly                          │
│  class InterpreterBackend(Backend):                                     │
│      env: Environment                                                   │
│                                                                         │
│      fn visit_expr(expr: HirExpr) -> Value:                            │
│          match expr:                                                    │
│              HirBinary(op, l, r) => self.eval_binop(op, l, r)          │
│              HirCall(fn, args) => self.eval_call(fn, args)             │
│              ...                                                        │
│                                                                         │
│  ─────────────────────────────────────────────────────────────────────  │
│                                                                         │
│  # sdn_backend.spl - NO-OP (data extraction only)                       │
│  class SdnBackend(Backend):                                             │
│      fn visit_expr(expr: HirExpr) -> SdnValue:                         │
│          match expr:                                                    │
│              HirLiteral(v) => SdnValue.from_literal(v)  # OK           │
│              HirCall(..) => raise Error("No code execution in SDN")    │
│              HirBinary(..) => raise Error("No code execution in SDN")  │
│              ...                                                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Data Flow: Same HIR, Different Outputs

```
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│                           Source Code                                   │
│                               │                                         │
│                               ▼                                         │
│                      ┌───────────────┐                                  │
│                      │    Lexer      │                                  │
│                      └───────┬───────┘                                  │
│                              │                                          │
│                              ▼                                          │
│                      ┌───────────────┐                                  │
│                      │  TreeSitter   │                                  │
│                      └───────┬───────┘                                  │
│                              │                                          │
│                              ▼                                          │
│                      ┌───────────────┐                                  │
│                      │    Parser     │                                  │
│                      └───────┬───────┘                                  │
│                              │                                          │
│                              ▼                                          │
│                      ┌───────────────┐                                  │
│                      │   AST → HIR   │                                  │
│                      └───────┬───────┘                                  │
│                              │                                          │
│                              ▼                                          │
│  ╔═══════════════════════════════════════════════════════════════════╗ │
│  ║                      HIR (SHARED)                                 ║ │
│  ║                                                                   ║ │
│  ║   HirModule { functions, structs, enums, imports }               ║ │
│  ║   HirFunction { name, params, body: Vec<HirStmt>, return_type }  ║ │
│  ║   HirExpr { Binary, Call, Literal, Ident, ... }                  ║ │
│  ║                                                                   ║ │
│  ╚═══════════════════════════════════════════════════════════════════╝ │
│                              │                                          │
│              ┌───────────────┼───────────────┐                         │
│              │               │               │                         │
│              ▼               ▼               ▼                         │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐              │
│  │   COMPILER    │  │  INTERPRETER  │  │      SDN      │              │
│  │    MODE       │  │     MODE      │  │     MODE      │              │
│  │               │  │               │  │               │              │
│  │  HIR.visit(   │  │  HIR.visit(   │  │  HIR.visit(   │              │
│  │   Compiler    │  │   Interp      │  │   Sdn         │              │
│  │   Backend)    │  │   Backend)    │  │   Backend)    │              │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘              │
│          │                  │                  │                       │
│          ▼                  ▼                  ▼                       │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐              │
│  │      MIR      │  │    Value      │  │   SdnValue    │              │
│  │   (lowered)   │  │  (executed)   │  │  (data only)  │              │
│  └───────┬───────┘  └───────────────┘  └───────────────┘              │
│          │                                                             │
│          ▼                                                             │
│  ┌───────────────┐                                                     │
│  │   Codegen     │                                                     │
│  │  (Cranelift)  │                                                     │
│  └───────┬───────┘                                                     │
│          │                                                             │
│          ▼                                                             │
│     Native Code                                                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## DI Configuration for Each Mode

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    DI PROFILE CONFIGURATION                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  # Compiler mode (default)                                              │
│  profile "compile":                                                     │
│      di.bind(Backend, CompilerBackend)                                 │
│      di.bind(Logger, ProductionLogger)                                 │
│      di.bind(MirBuilder, CraneliftMirBuilder)                          │
│                                                                         │
│  # Interpreter mode                                                     │
│  profile "interpret":                                                   │
│      di.bind(Backend, InterpreterBackend)                              │
│      di.bind(Logger, DebugLogger)                                      │
│      di.bind(Environment, RuntimeEnvironment)                          │
│                                                                         │
│  # SDN mode (data only, NO CODE EXECUTION)                              │
│  profile "sdn":                                                         │
│      di.bind(Backend, SdnBackend)          # Blocks all code paths     │
│      di.bind(Logger, SdnLogger)            # Minimal logging           │
│      di.bind(ValueFactory, SdnValueFactory)# Data-only values          │
│                                                                         │
│  # Development mode                                                     │
│  profile "dev":                                                         │
│      di.bind(Backend, InterpreterBackend)  # Fast iteration            │
│      di.bind(Logger, VerboseLogger)        # Full logging              │
│                                                                         │
│  # Test mode                                                            │
│  profile "test":                                                        │
│      di.bind(Backend, InterpreterBackend)                              │
│      di.bind(Logger, TestLogger)           # Capture for assertions    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Full Compiler Setup Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    COMPILER INITIALIZATION                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. LOAD CONFIG                                                         │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │  config = Config.load("simple.sdn")                         │    │
│     │  config.merge_env()           # SIMPLE_* env vars           │    │
│     │  config.merge_args(args)      # --profile=dev, etc          │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  2. SETUP DI CONTAINER                                                  │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │  di = DiContainer(profile: config.profile)                  │    │
│     │                                                             │    │
│     │  # Profile-specific bindings                                │    │
│     │  match config.profile:                                      │    │
│     │      "dev":                                                 │    │
│     │          di.bind(HirInst, FullHirInst)                     │    │
│     │          di.bind(Logger, DebugLogger)                      │    │
│     │      "sdn":                                                 │    │
│     │          di.bind(HirInst, SdnHirInst)   # NO-OP!           │    │
│     │          di.bind(Logger, SdnLogger)                        │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  3. SETUP AOP (Logging)                                                 │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │  aop = AopWeaver(di.resolve(Logger))                        │    │
│     │                                                             │    │
│     │  # Weave logging into compiler functions                    │    │
│     │  aop.around("parse_*", LogAspect(level: TRACE))            │    │
│     │  aop.around("emit_*", LogAspect(level: DEBUG))             │    │
│     │  aop.around("eval_*", LogAspect(level: VERBOSE))           │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  4. CREATE COMPILER INSTANCE                                            │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │  compiler = Compiler(                                       │    │
│     │      lexer:      di.resolve(Lexer),                        │    │
│     │      treesitter: di.resolve(TreeSitter),                   │    │
│     │      parser:     di.resolve(Parser),                       │    │
│     │      hir_data:   di.resolve(HirData),                      │    │
│     │      hir_inst:   di.resolve(HirInst),    # Full or NoOp    │    │
│     │      codegen:    di.resolve(Codegen),                      │    │
│     │      logger:     di.resolve(Logger),                       │    │
│     │  )                                                          │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  5. COMPILE                                                             │
│     ┌─────────────────────────────────────────────────────────────┐    │
│     │  result = compiler.compile(source)                          │    │
│     └─────────────────────────────────────────────────────────────┘    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Complete Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SIMPLE PROGRAMS (.spl)                          │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                     INFRASTRUCTURE                                │ │
│  │   config.spl ──► di.spl ──► aop.spl ──► log.spl                  │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                              │                                          │
│                              ▼                                          │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                     PARSING PIPELINE                              │ │
│  │   lexer.spl ──► treesitter.spl ──► parser.spl ──► ast.spl        │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                              │                                          │
│                              ▼                                          │
│  ╔═══════════════════════════════════════════════════════════════════╗ │
│  ║                        hir.spl (SHARED)                           ║ │
│  ║   HirModule, HirFunction, HirExpr, HirStmt, TypeInfo, Symbols    ║ │
│  ╚═══════════════════════════════════════════════════════════════════╝ │
│                              │                                          │
│              ┌───────────────┼───────────────┐                         │
│              │               │               │                         │
│              ▼               ▼               ▼                         │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐              │
│  │  COMPILER     │  │  INTERPRETER  │  │     SDN       │              │
│  │  BACKEND      │  │    BACKEND    │  │   BACKEND     │              │
│  │               │  │               │  │   (NO-OP)     │              │
│  │ compiler_     │  │ interpreter_  │  │ sdn_          │              │
│  │ backend.spl   │  │ backend.spl   │  │ backend.spl   │              │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘              │
│          │                  │                  │                       │
│          ▼                  ▼                  ▼                       │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐              │
│  │   mir.spl     │  │    Value      │  │   SdnValue    │              │
│  │   (lowering)  │  │  (execution)  │  │  (data only)  │              │
│  └───────┬───────┘  └───────────────┘  └───────────────┘              │
│          │                                                             │
│          ▼                                                             │
│  ┌───────────────┐                                                     │
│  │ codegen.spl   │                                                     │
│  └───────┬───────┘                                                     │
│          │                                                             │
│          ▼                                                             │
│   extern fn rt_*  (FFI calls)                                          │
└──────────┼──────────────────────────────────────────────────────────────┘
           │
┌──────────▼──────────────────────────────────────────────────────────────┐
│                    RUST FFI LAYER (Minimal)                             │
│                                                                         │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────────────┐ │
│  │ Codegen FFI     │  │ Runtime FFI     │  │ Platform FFI            │ │
│  │ rt_cranelift_*  │  │ rt_gc_*         │  │ rt_file_*, rt_net_*     │ │
│  │ rt_llvm_*       │  │ rt_alloc_*      │  │ rt_process_*, rt_env_*  │ │
│  └─────────────────┘  └─────────────────┘  └─────────────────────────┘ │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Module Dependency Graph

```
                              config.spl
                                  │
                                  ▼
                               di.spl ◄────────────────────────────┐
                                  │                                │
                    ┌─────────────┼─────────────┐                  │
                    │             │             │                  │
                    ▼             ▼             ▼                  │
               aop.spl       log.spl       (profiles)              │
                    │             │             │                  │
                    └─────────────┴─────────────┘                  │
                                  │                                │
                                  ▼                                │
                            lexer.spl                              │
                                  │                                │
                                  ▼                                │
                          treesitter.spl                           │
                                  │                                │
                                  ▼                                │
                            parser.spl                             │
                                  │                                │
                                  ▼                                │
                             ast.spl                               │
                                  │                                │
                                  ▼                                │
  ╔═══════════════════════════════════════════════════════════════╗│
  ║                      hir.spl (SHARED)                         ║│
  ║                                                               ║│
  ║  HirModule, HirFunction, HirExpr, HirStmt                    ║│
  ║  TypeInfo, SymbolTable, StructLayout, EnumLayout             ║│
  ║                                                               ║│
  ║  trait Backend:                                               ║│
  ║      fn visit_function(hir_fn) -> Result                     ║│
  ║      fn visit_expr(expr) -> Result                           ║│
  ╚═══════════════════════════════════════════════════════════════╝│
                                  │                                │
              ┌───────────────────┼───────────────────┐            │
              │                   │                   │            │
              ▼                   ▼                   ▼            │
  ┌───────────────────┐ ┌─────────────────┐ ┌─────────────────┐   │
  │ compiler_backend  │ │interpreter_back │ │  sdn_backend    │   │
  │      .spl         │ │    end.spl      │ │     .spl        │   │
  │                   │ │                 │ │                 │   │
  │ impl Backend      │ │ impl Backend    │ │ impl Backend    │   │
  │   HIR → MIR       │ │   HIR → Value   │ │   HIR → Data    │   │
  │                   │ │                 │ │   (NO-OP)       │   │
  └─────────┬─────────┘ └────────┬────────┘ └────────┬────────┘   │
            │                    │                   │             │
            │                    │                   │             │
            ▼                    ▼                   ▼             │
       mir.spl            runtime Value         SdnValue          │
            │                                                      │
            ▼                                                      │
      codegen.spl                                                  │
            │                                                      │
            ▼                                                      │
    rt_cranelift_* (FFI)                  DI binds Backend ────────┘
```

---

## AOP Weaving: Which Layer?

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    AOP WEAVING PIPELINE                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  Source Code                                                            │
│       │                                                                 │
│       ▼                                                                 │
│  ┌─────────────┐                                                        │
│  │   PARSER    │  Parses `pc { ... }` blocks into AopAdvice AST nodes  │
│  │             │  (rust/parser/src/ast/aop.rs)                          │
│  └──────┬──────┘                                                        │
│         │                                                               │
│         ▼                                                               │
│  ┌─────────────┐                                                        │
│  │     HIR     │  lower_aop_constructs() collects pointcut/advice      │
│  │  LOWERING   │  into unified predicates                               │
│  │             │  (rust/compiler/src/hir/lower/module_lowering/         │
│  │             │   module_pass.rs:207)                                   │
│  └──────┬──────┘                                                        │
│         │                                                               │
│         ▼                                                               │
│  ┌─────────────┐                                                        │
│  │  PREDICATE  │  Unified predicate system matches join points         │
│  │   MATCHING  │  (rust/compiler/src/predicate.rs:92)                  │
│  └──────┬──────┘                                                        │
│         │                                                               │
│         ▼                                                               │
│  ╔═════════════╗  ◄── WEAVING HAPPENS HERE (MIR level)                 │
│  ║  MIR WEAVER ║  insert_advice_calls() splices before/after/around    │
│  ║             ║  calls directly into MIR instruction blocks            │
│  ║             ║  (rust/compiler/src/weaving/weaver.rs:107)            │
│  ╚══════╤══════╝                                                        │
│         │                                                               │
│         ▼                                                               │
│    Woven MIR → Codegen / Interpreter                                    │
│                                                                         │
│  KEY: Weaving is at the MIR level, NOT AST or HIR.                     │
│  AST only parses the `pc{}` syntax. HIR collects predicates.           │
│  MIR is where advice calls are physically inserted into code.          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Contracts: Which Layer?

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    CONTRACT ASSERTION PIPELINE                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  HIR TYPES    HirContract { pre, post, invariant }                     │
│               (rust/compiler/src/hir/types/contracts.rs)               │
│                    │                                                    │
│                    ▼                                                    │
│  HIR LOWERING lower_contract() transforms contract AST → HIR          │
│               (rust/compiler/src/hir/lower/module_lowering/            │
│                contract.rs:141)                                         │
│                    │                                                    │
│                    ▼                                                    │
│  MIR EMISSION emit_entry_contracts() / emit_exit_contracts()           │
│               Emits ContractCheck + ContractOldCapture instructions    │
│               (rust/compiler/src/mir/lower/lowering_contracts.rs)      │
│               (rust/compiler/src/mir/inst_enum.rs:646)                 │
│                    │                                                    │
│                    ▼                                                    │
│  RUNTIME FFI  simple_contract_check() raises on violation              │
│               (rust/runtime/src/value/ffi/contracts.rs:69)             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## DI vs AOP: Separate Systems

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    DI AND AOP RELATIONSHIP                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  DI and AOP are SEPARATE systems that coordinate, not overlap:         │
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  DI (Dependency Injection)                                       │   │
│  │  • Binds interfaces to implementations (Backend trait → impl)   │   │
│  │  • Profile-based: dev/test/prod/sdn select different bindings   │   │
│  │  • Operates at OBJECT CONSTRUCTION time                          │   │
│  │  • Does NOT use AOP internally                                   │   │
│  │  • Does NOT modify code — only selects which code to run         │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  AOP (Aspect-Oriented Programming)                               │   │
│  │  • Weaves cross-cutting concerns (logging, tracing, contracts)  │   │
│  │  • Operates at MIR COMPILATION time (modifies instruction flow) │   │
│  │  • Uses unified predicates to match join points                  │   │
│  │  • DI-injected logger is USED BY AOP (DI provides the logger,  │   │
│  │    AOP decides where to call it)                                 │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  Coordination flow:                                                    │
│    config.spl → di.spl (binds Logger impl) → aop.spl (uses Logger)   │
│                                                                         │
│  DI does NOT use AOP. AOP uses DI-provided services.                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Current Implementation: Rust (Target: Simple)

The AOP/contract/DI pipeline is currently implemented in **Rust**, as part of the
compiler crate. The target architecture (described in this document) envisions
rewriting these as Simple modules (`aop.spl`, `di.spl`, `config.spl`), but the
current working implementation lives in:

| Component | Current (Rust) | Target (Simple) |
|-----------|---------------|-----------------|
| AOP Weaver | `rust/compiler/src/weaving/weaver.rs` | `aop.spl` |
| Predicates | `rust/compiler/src/predicate.rs` | Part of `aop.spl` |
| Contracts | `rust/compiler/src/hir/types/contracts.rs` | Part of `hir.spl` |
| Contract MIR | `rust/compiler/src/mir/lower/lowering_contracts.rs` | Part of `mir.spl` |
| DI Container | Design only (profile-based binding) | `di.spl` |
| Config | `simple.sdn` loading via Rust SDN crate | `config.spl` |

---

## Summary: Key Architecture Points

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         KEY ARCHITECTURE                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. LEXER → TREESITTER → PARSER                                         │
│     TreeSitter does outline parsing, Parser fills in details            │
│                                                                         │
│  2. HIR IS SHARED                                                       │
│     Same HIR representation for compiler, interpreter, SDN              │
│     Different backends process HIR differently                          │
│                                                                         │
│  3. BACKEND TRAIT (DI INJECTED)                                         │
│     ┌────────────────┬────────────────┬────────────────┐               │
│     │ CompilerBackend│ InterpBackend  │ SdnBackend     │               │
│     │ HIR → MIR      │ HIR → Value    │ HIR → Data     │               │
│     │ → Codegen      │ → Execute      │ → NO-OP        │               │
│     └────────────────┴────────────────┴────────────────┘               │
│                                                                         │
│  4. CONFIG → DI → AOP (separate systems, coordinated)                   │
│     Config loads settings, DI binds implementations,                    │
│     AOP weaves cross-cutting concerns at MIR level                     │
│     DI does NOT use AOP; AOP uses DI-provided services                 │
│                                                                         │
│  5. AOP WEAVING AT MIR LEVEL                                            │
│     Parse pc{} → HIR predicates → MIR advice insertion                 │
│     Contracts also emit MIR instructions (ContractCheck)               │
│                                                                         │
│  6. SDN SAFETY                                                          │
│     SdnBackend blocks all code execution paths                         │
│     Only literal data values allowed                                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## What MUST Stay in Rust (Minimal)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    RUST ONLY (Bootstrapping + Low-Level FFI)            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. BOOTSTRAP PARSER (needed to compile Simple compiler)                │
│     └── Lexer, Parser, AST (minimal, just enough to bootstrap)          │
│                                                                         │
│  2. CODEGEN BINDINGS (C FFI to native libraries)                        │
│     ├── Cranelift bindings                                              │
│     ├── LLVM bindings (inkwell)                                         │
│     └── Object file generation                                          │
│                                                                         │
│  3. RUNTIME CORE (low-level memory management)                          │
│     ├── GC implementation (mark-sweep, memory allocation)               │
│     ├── RuntimeValue (NaN-boxing, tagged pointers)                      │
│     └── Platform FFI (OS calls, file I/O, networking)                   │
│                                                                         │
│  4. SHARED TYPES (hir-core - type definitions only)                     │
│     └── LogLevel, ValueKind, StructLayout, TokenKind                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## What Should Be SIMPLE (Everything Else)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    SIMPLE IMPLEMENTATION (Target)                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  COMPILER (rewrite in Simple when self-hosting)                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  parser.spl        - Lexer, Parser, AST construction            │   │
│  │  type_checker.spl  - Type inference, type checking              │   │
│  │  hir.spl           - HIR construction and transforms            │   │
│  │  mir.spl           - MIR lowering and optimization              │   │
│  │  codegen.spl       - Code generation (calls Cranelift FFI)      │   │
│  │  interpreter.spl   - Tree-walking interpreter                   │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  STANDARD LIBRARY (already in Simple)                                   │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  log.spl, db.spl, config.spl, di.spl, time.spl                  │   │
│  │  map.spl, set.spl, list.spl, string.spl                         │   │
│  │  file.spl, net.spl, json.spl, regex.spl                         │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  TOOLS (already in Simple)                                              │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  cli/main.spl      - Command line interface                     │   │
│  │  sdn/main.spl      - SDN tool                                   │   │
│  │  formatter.spl     - Code formatter                             │   │
│  │  linter.spl        - Code linter                                │   │
│  │  lsp.spl           - Language server                            │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│  PARSERS (rewrite in Simple)                                            │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  sdn_parser.spl    - SDN data format parser                     │   │
│  │  json_parser.spl   - JSON parser                                │   │
│  │  toml_parser.spl   - TOML parser (if needed)                    │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Target Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SIMPLE PROGRAMS (.spl)                          │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                     COMPILER (in Simple)                          │ │
│  │  parser.spl → type_checker.spl → hir.spl → mir.spl → codegen.spl │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                     STANDARD LIBRARY (in Simple)                  │ │
│  │  log, db, config, di, time, map, set, file, net, json, regex     │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
│  ┌───────────────────────────────────────────────────────────────────┐ │
│  │                     TOOLS & APPS (in Simple)                      │ │
│  │  cli, sdn, formatter, linter, lsp, test runner                   │ │
│  └───────────────────────────────────────────────────────────────────┘ │
│                                    │                                    │
│                                    ▼                                    │
│                        extern fn rt_* (FFI calls)                       │
└────────────────────────────────────┼────────────────────────────────────┘
                                     │
┌────────────────────────────────────▼────────────────────────────────────┐
│                    RUST FFI LAYER (Minimal)                             │
│                                                                         │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────────────┐ │
│  │ Codegen FFI     │  │ Runtime FFI     │  │ Platform FFI            │ │
│  │ rt_cranelift_*  │  │ rt_gc_*         │  │ rt_file_*, rt_net_*     │ │
│  │ rt_llvm_*       │  │ rt_alloc_*      │  │ rt_process_*, rt_env_*  │ │
│  └─────────────────┘  └─────────────────┘  └─────────────────────────┘ │
│                                                                         │
└────────────────────────────────────┼────────────────────────────────────┘
                                     │
┌────────────────────────────────────▼────────────────────────────────────┐
│                    RUST CORE (Minimal, Low-Level Only)                  │
│                                                                         │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌───────────────┐  │
│  │ Bootstrap   │  │ Cranelift   │  │ GC/Memory   │  │ hir-core      │  │
│  │ Parser      │  │ + LLVM      │  │ Management  │  │ (types only)  │  │
│  │ (temporary) │  │ Bindings    │  │             │  │               │  │
│  └─────────────┘  └─────────────┘  └─────────────┘  └───────────────┘  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Migration Plan: Rust → Simple

### Migration Status (Updated 2026-01-31)

**All phases complete.** Simple compiler pipeline is self-hosted.

| Component | Simple File(s) | Lines | Status |
|-----------|---------------|-------|--------|
| Lexer | `lexer.spl` | 1,250 | ✅ Done |
| Parser | `parser.spl` | 1,809 | ✅ Done |
| TreeSitter | `treesitter.spl` | 1,333 | ✅ Done |
| Type Inference | `type_infer.spl` | 1,478 | ✅ Done |
| HIR | `hir_types.spl` + `hir_definitions.spl` + `hir_lowering.spl` | 2,107 | ✅ Done |
| MIR | `mir_data.spl` + `mir_lowering.spl` | 1,526 | ✅ Done |
| Backend | `backend.spl` | 842 | ✅ Done |
| Codegen | `codegen.spl` | 758 | ✅ Done |
| Resolve | `resolve.spl` | 786 | ✅ Done |
| Driver | `driver.spl` | 591 | ✅ Done |
| Interpreter | `src/app/interpreter/` (65 files) | ~8,000 | ✅ Done |
| CLI | `src/app/cli/main.spl` | 552 | ✅ Done |
| Formatter | `src/app/formatter/` | - | ✅ Done |
| Linter/Fix | `src/app/lint/` + `src/app/fix/` | - | ✅ Done |
| Test Runner | `src/app/test_runner_new/` (8 files) | - | ✅ Done |
| LSP | `src/app/lsp/` | - | 🔄 In Progress |
| DAP | `src/app/dap/` | - | 🔄 In Progress |

**Note:** `hir.spl` (29 lines) and `mir.spl` (22 lines) are re-export modules.
Actual logic is in the split files listed above.

**Additional compiler modules:**
- `blocks/` - Custom grammar blocks (builtin, registry, resolver)
- `monomorphize/` - Generic monomorphization (deferred, partition, tracker, cycle_detector)
- `linker/` - Linking (link, mold, smf_reader, obj_taker)
- `loader/` - Module loading (module_loader, jit_instantiator)
- `dependency/` - Dependency analysis (graph, resolution, visibility, symbol)

**Total compiler: ~27,423 lines. Total apps: ~38,029 lines.**

---

## FFI Design (Thin Layer)

The Rust FFI layer should be **minimal** - just expose low-level operations that Simple cannot do itself.

### Codegen FFI (calls to Cranelift/LLVM)

```
Simple (codegen.spl)              Rust FFI
────────────────────              ────────
emit_function(name, body)    →    rt_cranelift_emit_function()
emit_basic_block(label)      →    rt_cranelift_emit_block()
emit_instruction(opcode)     →    rt_cranelift_emit_inst()
finalize_module()            →    rt_cranelift_finalize()
```

### GC FFI (memory management)

```
Simple (runtime)                  Rust FFI
────────────────                  ────────
(automatic)                  →    rt_gc_alloc(size, type)
(automatic)                  →    rt_gc_collect()
(automatic)                  →    rt_gc_root_add(ptr)
```

### Platform FFI (OS operations)

```
Simple (file.spl, net.spl)        Rust FFI
──────────────────────────        ────────
file.read(path)              →    rt_file_read(path)
file.write(path, data)       →    rt_file_write(path, data)
net.connect(host, port)      →    rt_tcp_connect(host, port)
```

---

## Line Count Comparison (Rust vs Simple - Actual)

| Component | Rust (src/rust/) | Simple (simple/compiler/) | Ratio |
|-----------|-----------------|--------------------------|-------|
| Lexer | ~2,000 | 1,250 | 63% |
| Parser | ~8,000 (AST: 950) | 1,809 | 23% |
| TreeSitter | N/A | 1,333 | New |
| Type Inference | ~5,000 | 1,478 | 30% |
| HIR | ~3,000 (types: 501) | 2,107 (3 files) | 70% |
| MIR | ~6,000 (inst: 869) | 1,526 (2 files) | 25% |
| Interpreter | ~10,000 | ~8,000 (65 files) | 80% |
| Codegen | ~5,000 (Cranelift) | 758 (+ FFI calls) | 15% |
| **Total Compiler** | **~28,000** | **~8,200** | **71%** |

**Note**: Simple code is more concise due to:
- No lifetime annotations
- Pattern matching syntax
- Less boilerplate
- Higher-level abstractions

---

## Completed Phases (Infrastructure)

### Phase 1: Connect hir-core (COMPLETE)
- [x] Create `simple-hir-core` crate
- [x] Add LogLevel, StructLayout, EnumLayout
- [x] Link to all crates

### Phase 2: Add log FFI (COMPLETE)
- [x] Implement `log_ffi.rs` in runtime
- [x] Connect `log.spl` to FFI

### Phase 3: Add TokenKind sharing (COMPLETE)
- [x] Add TokenCategory, BaseTokenKind to hir-core

### Phase 4: Add ValueKind sharing (COMPLETE)
- [x] Add ValueKind enum to hir-core
- [x] Add value_kind() to Value and RuntimeValue

---

## Next Steps: Self-Hosting

### Step 1: Write Lexer in Simple
```simple
# simple/compiler/lexer.spl
class Lexer:
    source: text
    pos: i64

    fn next_token() -> Token:
        self.skip_whitespace()
        match self.peek():
            '(' => Token(LParen, self.pos)
            ')' => Token(RParen, self.pos)
            '+' => Token(Plus, self.pos)
            ...
```

### Step 2: Write Parser in Simple
```simple
# simple/compiler/parser.spl
class Parser:
    lexer: Lexer
    current: Token

    fn parse_expr() -> Expr:
        match self.current.kind:
            IntLit => self.parse_int()
            Ident => self.parse_ident_or_call()
            LParen => self.parse_grouped()
            ...
```

### Step 3: Bootstrap
1. Use Rust parser to compile Simple lexer/parser
2. Use Simple lexer/parser to compile itself
3. Verify output matches
4. Remove Rust parser (keep only for bootstrapping new installations)

---

## Benefits of Simple-First Architecture

1. **Single language** - Developers only need to know Simple
2. **Faster iteration** - Simple has better syntax, easier to modify
3. **Smaller codebase** - Simple is more concise than Rust
4. **Dogfooding** - Using Simple to build Simple catches bugs
5. **No performance penalty** - LLVM compilation means same speed
6. **Easier contribution** - Lower barrier to entry than Rust

---

## What Stays in Rust Forever

Only these components remain in Rust permanently:

| Component | Reason |
|-----------|--------|
| Cranelift/LLVM bindings | C FFI, no Simple equivalent |
| GC implementation | Low-level memory management |
| RuntimeValue (NaN-boxing) | Bit manipulation, performance critical |
| Platform FFI | OS system calls |
| Bootstrap parser | Needed to compile first Simple compiler |
| hir-core types | Shared between Rust FFI and Simple |

Everything else should eventually be Simple.
