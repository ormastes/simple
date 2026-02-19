# Compiler MDSoC Design: Dimension Transforms Across Pipeline Stages

> Applying MDSoC (Multi-Dimensional Separation of Concerns) and Clean Architecture
> to the Simple compiler pipeline.
>
> Extends `mdsoc_design.md` with a concrete compiler-specific dimension mapping.

**Version:** 1.0
**Date:** 2026-02-17
**Status:** Design / Implementation Plan

---

## 1. Problem: Compiler Pipeline Has the Same "Two-Ends" Problem

The compiler has its own version of "UI + DB both touch the world":

```
SOURCE TEXT                                 MACHINE CODE
   (volatile:                                  (volatile:
    language                                    target arch,
    syntax)                                     ABI, OS)
       │                                           │
       ↓                                           ↑
  ┌─────────────────────────────────────────────────┐
  │             PIPELINE STAGES                     │
  │  Lexer → Parser → Desugar → TypeCheck           │
  │       → HIR → MIR → Optimize → Backend         │
  └─────────────────────────────────────────────────┘
```

Each stage has a **different data structure** (Token, AST, HIR, MIR) and a different
**decomposition axis**:

| Axis | Question |
|------|----------|
| By **stage** | What phase of compilation is this? |
| By **IR structure** | What data node type is being handled? |
| By **concern** | What semantic concept is being analyzed? |
| By **target** | What machine/runtime is being targeted? |

These decompositions **naturally mismatch** at stage boundaries — exactly the dim-transform problem.

---

## 2. Mapping MDSoC Dimensions to Compiler

### 2.1 The Three Dimensions

**Dimension `D_entity` → IR Structures (stable)**

Domain entities = the IR types themselves. These are stable and shared across stages.

```
entity/
  token/          # Token kinds and token stream
  ast/            # AST node types (expr, stmt, decl arenas)
  hir/            # HIR types (typed AST with explicit types)
  mir/            # MIR types (instruction-level, basic blocks)
  type_system/    # Core type representation
  span/           # Source location tracking
```

**Dimension `D_feature` → Pipeline Stages (volatile)**

Each stage is a vertical slice: it owns its UI (entry point), logic, and port definitions.

```
feature/
  lexing/         # Source text → Token stream
  parsing/        # Token stream → AST
  desugaring/     # AST → Desugared AST (5 passes)
  type_checking/  # AST → Typed AST (inference + validation)
  monomorphization/  # Typed AST → Monomorphic AST
  hir_lowering/   # Typed AST → HIR
  mir_lowering/   # HIR → MIR (basic blocks)
  optimization/   # MIR → Optimized MIR
  codegen/        # MIR → Backend output
  linking/        # Object files → Executable
```

**Dimension `D_transform` → Stage Boundary Adapters**

Each stage boundary is a transform: it bridges the output type of stage N with the
input type expected by stage N+1. Mismatches (different IR shape, different terminology,
different granularity) are resolved here.

```
transform/
  feature/
    lexing_to_parsing/          # Token stream → AST-ready input
    parsing_to_desugaring/      # AST → desugar pipeline input
    desugaring_to_typing/       # Desugared AST → type-check input
    typing_to_hir/              # Typed AST → HIR (MAJOR mismatch)
    hir_to_mir/                 # HIR → MIR (MAJOR mismatch)
    mir_to_backend/             # MIR → backend-specific IR (MAJOR mismatch)
    mir_to_optimizer/           # MIR → optimization pass input
    backend_to_linker/          # Object file → linker input
```

### 2.2 Why Stage Boundaries are the Natural Transform Points

The **biggest structural mismatches** occur at:

**`typing_to_hir` (Typed AST → HIR)**
- AST: tree-structured, source-oriented, with implicit types
- HIR: typed, name-resolved, desugared implicit returns, with symbol table
- Mismatch: HIR has explicit type on every node; AST doesn't

**`hir_to_mir` (HIR → MIR)**
- HIR: structured control flow (`if`, `for`, `match` as nodes)
- MIR: flat basic blocks with explicit jumps/gotos
- Mismatch: control flow is fundamentally different representation

**`mir_to_backend` (MIR → Target)**
- MIR: target-independent three-address code
- Backend: target-specific (x86 registers, LLVM types, Cranelift values, WASM stack)
- Mismatch: conceptually the same operation; radically different representation

---

## 3. Proposed Directory Structure

### 3.1 Compiler Source Layout

```
src/
  # Entity dimension: stable IR types
  core/
    entity/
      token/
        mod.spl                  # Re-exports token types
        kinds.spl                # Token kind enum + constants
        stream.spl               # TokenStream type
        __init__.spl
      ast/
        mod.spl
        expr.spl                 # Expr node (arena + struct)
        stmt.spl                 # Stmt node
        decl.spl                 # Decl node
        arena.spl                # Parallel arrays (seed-compat)
        __init__.spl
      hir/
        mod.spl
        types.spl                # HIR type system (CoreHirType)
        node.spl                 # Typed HIR nodes
        symbol_table.spl         # Symbol table types
        __init__.spl
      mir/
        mod.spl
        inst.spl                 # MIR instruction (CoreMirInst)
        block.spl                # Basic block (CoreBasicBlock)
        func.spl                 # MIR function (CoreMirFunction)
        __init__.spl
      types/
        mod.spl
        core_types.spl           # Core type tags + constants
        generic.spl              # Generic type representation
        __init__.spl
      span/
        mod.spl
        span.spl                 # Source span (file, line, col)
        __init__.spl

  # Feature dimension: pipeline stages
  compiler/
    feature/
      lexing/
        ui/
          lexer_cli.spl          # CLI entry: lex-only mode
        app/
          lexer.spl              # Lexer logic (was src/compiler_core/lexer.spl)
          lexer_struct.spl       # Lexer state struct
          ports.spl              # LexerInputPort, LexerOutputPort
        __init__.spl
      parsing/
        ui/
          parser_cli.spl         # CLI entry: parse-only mode
        app/
          parser.spl             # Parser logic (was src/compiler_core/parser.spl)
          ports.spl              # ParserInputPort, ParserOutputPort
        __init__.spl
      desugaring/
        ui/
          desugar_cli.spl
        app/
          mod.spl                # 5-pass pipeline orchestrator
          forwarding.spl         # Pass 0: strip aliases
          static_constants.spl   # Pass 1: extract static vals
          static_methods.spl     # Pass 2: extract static fns
          enum_constructors.spl  # Pass 3: enum factory fns
          rewriter.spl           # Pass 4: rewrite call sites
          ports.spl              # DesugarInputPort, DesugarOutputPort
        __init__.spl
      type_checking/
        ui/
          typecheck_cli.spl
        app/
          type_checker.spl       # Type checking (was src/compiler_core/type_checker.spl)
          type_inference.spl     # Type inference
          ports.spl
        __init__.spl
      monomorphization/
        ui/
          mono_cli.spl
        app/
          generic_runtime.spl    # Runtime monomorphization
          type_erasure.spl       # Compile-time erasure
          ast_clone.spl          # AST cloning
          type_subst.spl         # Type substitution
          ports.spl
        __init__.spl
      hir_lowering/
        ui/
          hir_cli.spl
        app/
          hir_lower.spl          # AST → HIR lowering
          name_resolver.spl      # Name resolution pass
          implicit_return.spl    # Implicit return insertion
          ports.spl
        __init__.spl
      mir_lowering/
        ui/
          mir_cli.spl
        app/
          mir_lower.spl          # HIR → MIR lowering
          cfg_builder.spl        # Control flow graph construction
          bb_builder.spl         # Basic block construction
          ports.spl
        __init__.spl
      optimization/
        ui/
          opt_cli.spl
        app/
          pass_manager.spl       # Optimization pass manager
          dead_code.spl          # DCE pass
          constant_folding.spl   # Constant folding
          inline.spl             # Inlining
          ports.spl
        __init__.spl
      codegen/
        ui/
          codegen_cli.spl
        app/
          driver.spl             # Codegen driver
          backend_selector.spl   # Backend selection
          ports.spl              # BackendPort
        backends/
          llvm/
            backend.spl
            ir_builder.spl
          cranelift/
            backend.spl
          wasm/
            backend.spl
          native/
            backend.spl
            x86_64.spl
            aarch64.spl
          cuda/
            backend.spl
          vulkan/
            backend.spl
          lean/
            backend.spl
        __init__.spl
      linking/
        ui/
          link_cli.spl
        app/
          linker.spl
          smf_reader.spl
          smf_writer.spl
          ports.spl
        __init__.spl

  # Transform dimension: stage boundary bridges
  compiler/
    transform/
      __init__.spl
      feature/
        __init__.spl
        lexing_to_parsing/
          __init__.spl
          entity_view/
            __init__.spl
            TokenStreamView.spl  # Token stream adapted for parser
        parsing_to_desugaring/
          __init__.spl
          entity_view/
            __init__.spl
            AstView.spl          # AST adapted for desugar (source+ast combo)
        typing_to_hir/
          __init__.spl
          entity_view/
            __init__.spl
            TypedAstView.spl     # Typed AST adapted for HIR lowering (MAJOR)
        hir_to_mir/
          __init__.spl
          entity_view/
            __init__.spl
            HirView.spl          # HIR adapted for MIR lowering (MAJOR)
        mir_to_backend/
          __init__.spl
          entity_view/
            __init__.spl
            MirView.spl          # MIR adapted per-backend (MAJOR)
```

---

## 4. Three Major Transform Examples

### 4.1 Transform: `typing_to_hir`

**Why needed:** AST nodes have implicit types + source orientation.
HIR needs explicit types on every node + name resolution.

**File: `src/compiler/transform/feature/typing_to_hir/entity_view/TypedAstView.spl`**

```simple
"""
TypedAst → HIR adapter.
Bridges the mismatch between the typed AST representation
and the HIR's explicit-typed, name-resolved nodes.
"""

# Re-export AST types (what HIR lowering needs to read from)
reexport compiler_core/entity/ast/expr.{Expr, EXPR_BINARY, EXPR_CALL, EXPR_IDENT}
reexport compiler_core/entity/ast/stmt.{Stmt, STMT_VAL, STMT_IF, STMT_FOR}
reexport compiler_core/entity/ast/decl.{Decl, DECL_FN, DECL_STRUCT}

# Re-export HIR types (what HIR lowering produces)
reexport compiler_core/entity/hir/types.{CoreHirType, HIR_TYPE_I64, HIR_TYPE_FN}
reexport compiler_core/entity/hir/symbol_table.{CoreSymbolTable, CoreSymbolEntry}

# Adapter: combined context for HIR lowering
struct TypedAstContext:
    """
    Combines type inference results with AST for HIR lowering.
    Provides the 'bridge' that HIR lowering needs without
    importing AST and type-checker directly.
    """
    ast_decls: [i64]          # Root declaration indices
    symbol_table: CoreSymbolTable
    inferred_types: [i64]     # Per-expression type index

    fn get_expr_type(expr_idx: i64) -> CoreHirType:
        """Look up inferred type for any expression."""
        val type_idx = self.inferred_types[expr_idx]
        self.symbol_table.resolve_type(type_idx)

    fn resolve_name(name: text, scope: i64) -> CoreSymbolEntry?:
        """Resolve identifier to symbol entry."""
        self.symbol_table.find(name, scope)

    static fn from_typed(ast, type_table, sym_table) -> TypedAstContext:
        """
        Factory: build context from type checker outputs.
        This is where the mismatch reconciliation happens.
        """
        TypedAstContext(
            ast_decls: ast.root_decls,
            symbol_table: sym_table,
            inferred_types: type_table.per_expr_type
        )
```

### 4.2 Transform: `hir_to_mir`

**Why needed:** HIR has structured control flow (`if/for/match` as tree nodes).
MIR needs flat basic blocks with explicit conditional jumps.

**File: `src/compiler/transform/feature/hir_to_mir/entity_view/HirView.spl`**

```simple
"""
HIR → MIR adapter.
Bridges the mismatch between HIR's tree-structured control flow
and MIR's flat basic-block representation.
"""

# Re-export HIR types (source)
reexport compiler_core/entity/hir/node.{HirIf, HirFor, HirMatch, HirBlock, HirExpr}
reexport compiler_core/entity/hir/types.{CoreHirType}

# Re-export MIR types (target)
reexport compiler_core/entity/mir/block.{CoreBasicBlock}
reexport compiler_core/entity/mir/inst.{CoreMirInst, MIR_JUMP, MIR_BRANCH, MIR_LABEL}
reexport compiler_core/entity/mir/func.{CoreMirFunction}

# Adapter: control flow shape
struct CfgContext:
    """
    Provides the structured → unstructured control flow bridge.
    HIR lowering uses this to emit basic blocks correctly
    without direct dependency on MIR types.
    """
    current_fn: CoreMirFunction
    loop_break_targets: [text]    # Stack of loop break labels
    loop_continue_targets: [text] # Stack of loop continue labels
    current_block: text           # Current basic block label

    fn enter_loop(break_label: text, continue_label: text):
        self.loop_break_targets.append(break_label)
        self.loop_continue_targets.append(continue_label)

    fn exit_loop():
        self.loop_break_targets.pop()
        self.loop_continue_targets.pop()

    fn current_break_target() -> text:
        self.loop_break_targets[self.loop_break_targets.len() - 1]

    fn current_continue_target() -> text:
        self.loop_continue_targets[self.loop_continue_targets.len() - 1]

    fn emit_jump(target: text):
        """Emit unconditional jump (goto) in current block."""
        val inst = CoreMirInst(kind: MIR_JUMP, s_val: target)
        self.current_fn.emit(inst)

    fn emit_branch(cond: i64, then_label: text, else_label: text):
        """Emit conditional branch in current block."""
        val inst = CoreMirInst(kind: MIR_BRANCH, src1: cond, s_val: then_label)
        self.current_fn.emit(inst)
```

### 4.3 Transform: `mir_to_backend`

**Why needed:** MIR is target-independent three-address code.
Each backend speaks a completely different "language" (LLVM IR, WASM stack, Cranelift values, register pairs).

**File: `src/compiler/transform/feature/mir_to_backend/entity_view/MirView.spl`**

```simple
"""
MIR → Backend adapter.
Provides a stable projection of MIR that backends can consume
without coupling to MIR internals.
"""

# Re-export MIR types (what backends read)
reexport compiler_core/entity/mir/inst.{CoreMirInst, MIR_ADD, MIR_SUB, MIR_CALL, MIR_LOAD}
reexport compiler_core/entity/mir/block.{CoreBasicBlock}
reexport compiler_core/entity/mir/func.{CoreMirFunction}

# Adapter: backend-neutral view of MIR program
struct MirProgram:
    """
    Backend-neutral view of a compiled MIR program.
    Backends should consume this view, not MIR internals.
    """
    functions: [CoreMirFunction]
    extern_fns: [text]
    string_literals: [text]
    debug_info: MirDebugInfo?

    fn main_function() -> CoreMirFunction?:
        for fn in self.functions:
            if fn.name == "main":
                return fn
        nil

    fn find_function(name: text) -> CoreMirFunction?:
        for fn in self.functions:
            if fn.name == name:
                return fn
        nil

struct MirDebugInfo:
    """Debug information attached to MIR for backends that support DWARF."""
    fn_to_source: [text]    # function name → source file
    fn_to_line: [i64]       # function name → start line

# Backend output port
struct BackendOutput:
    """
    What a backend produces.
    Abstracted so linker doesn't depend on specific backend types.
    """
    object_bytes: [i64]
    symbol_map: dict          # symbol name → offset
    relocation_table: [dict]
    debug_sections: dict?
    target_triple: text
```

---

## 5. Applying Standard Architecture to Compiler

### 5.1 Pipeline as Clean Architecture Layers

```
┌───────────────────────────────────────────────────┐
│     CLI / IDE / Build System (Inbound Adapters)   │  ← Volatile
└────────────────────────┬──────────────────────────┘
                         │
                         ↓
┌───────────────────────────────────────────────────┐
│          Compiler Driver (Application)            │
│   Orchestrates stages: lex → parse → ... → emit   │
│   Defines StagePort interfaces                    │
└────────────────────────┬──────────────────────────┘
                         │
                         ↓
┌───────────────────────────────────────────────────┐
│         Pipeline Stage Logic (Domain)             │
│   Lexer, Parser, TypeChecker, HirLowering...      │
│   Pure: Token → AST → HIR → MIR                  │
└───────────────────────────────────────────────────┘
                         ↑
                         │ implements
┌───────────────────────────────────────────────────┐
│         Backend Adapters (Outbound)               │
│   LLVM, Cranelift, WASM, Native, Lean, CUDA...    │
└───────────────────────────────────────────────────┘
```

### 5.2 Port Definitions per Stage

**Compiler-level ports:**

```simple
# src/compiler/feature/type_checking/app/ports.spl

struct TypeCheckerInputPort:
    """What type checking needs from the outside."""
    get_ast_fn: fn() -> AstModule
    get_desugar_output_fn: fn() -> DesugarOutput

struct TypeCheckerOutputPort:
    """What type checking produces."""
    get_typed_ast_fn: fn() -> TypedAstContext
    get_diagnostics_fn: fn() -> [Diagnostic]

# src/compiler/feature/hir_lowering/app/ports.spl

struct HirLoweringInputPort:
    """What HIR lowering needs from type checking output."""
    get_typed_context_fn: fn() -> TypedAstContext  # From transform

struct HirLoweringOutputPort:
    """What HIR lowering produces."""
    get_hir_module_fn: fn() -> HirModule
```

### 5.3 Feature `__init__.spl` for Each Stage

**Example: `src/compiler/feature/hir_lowering/__init__.spl`**

```simple
arch {
  dimension = "feature"
  layer = "app"

  uses_transform = "compiler/transform/feature/typing_to_hir"

  imports {
    allow = [
      "compiler/feature/hir_lowering/**",
      "compiler/transform/feature/typing_to_hir/**",  # Via transform only
      "compiler_core/entity/hir/**",                           # HIR output types
      "shared/**"
    ]
    deny = [
      "compiler_core/entity/ast/**",       # Must use transform view, not raw AST
      "compiler/feature/parsing/**",  # Stage isolation
      "compiler/backend/**"           # No backend in lowering
    ]
  }

  exports {
    expose = ["./app/hir_lower", "./app/ports"]
  }
}
```

---

## 6. Implementation Plan

### Phase 0: Preparation (No code changes)

- [ ] Verify existing tests pass (`bin/simple test`)
- [ ] Map exact current file → new location mapping
- [ ] Identify which files are seed-critical (can't be restructured)
- [ ] Create migration tracking in `doc/report/compiler_mdsoc_migration.md`

---

### Phase 1: Entity Dimension — Extract IR Types

**Goal:** Move stable IR data types into `src/compiler_core/entity/` subdirectories.

**Rationale:** IR types are the "domain" of the compiler. They must be
isolated from pipeline logic.

| Current File | New Location | Notes |
|---|---|---|
| `src/compiler_core/tokens.spl` | `src/compiler_core/entity/token/kinds.spl` | Token constants |
| `src/compiler_core/lexer_struct.spl` | `src/compiler_core/entity/token/stream.spl` | Lexer state struct |
| `src/compiler_core/ast.spl` (arena part) | `src/compiler_core/entity/ast/arena.spl` | Parallel arrays |
| `src/compiler_core/ast_types.spl` | `src/compiler_core/entity/ast/nodes.spl` | CoreExpr/Stmt/Decl |
| `src/compiler_core/hir_types.spl` | `src/compiler_core/entity/hir/types.spl` | CoreHirType + symbols |
| `src/compiler_core/mir_types.spl` | `src/compiler_core/entity/mir/types.spl` | CoreMirInst + blocks |
| `src/compiler_core/types.spl` | `src/compiler_core/entity/types/core_types.spl` | Type constants |

**Strategy:** Keep old paths as symlinks temporarily. Update imports incrementally.

**Deliverables:**
- `src/compiler_core/entity/` directory structure with `__init__.spl` configs
- All IR type tests passing
- Migration report updated

---

### Phase 2: Feature Dimension — Stage Modules

**Goal:** Give each pipeline stage a feature module with `ui/`, `app/`, and ports.

**Rationale:** Stages are the "use cases" of the compiler. Each should be
independently testable with mock ports.

**Substages:**

**Phase 2a: Lexing + Parsing (Simplest)**

```
src/compiler/feature/lexing/
  app/
    lexer.spl           # Moved from src/compiler_core/lexer.spl
    ports.spl           # LexerPort
  __init__.spl

src/compiler/feature/parsing/
  app/
    parser.spl          # Moved from src/compiler_core/parser.spl
    ports.spl           # ParserPort
  __init__.spl
```

**Phase 2b: Desugaring**

```
src/compiler/feature/desugaring/
  app/
    mod.spl             # Orchestrator (was src/app/desugar/mod.spl)
    forwarding.spl
    static_constants.spl
    static_methods.spl
    enum_constructors.spl
    rewriter.spl
    ports.spl
  __init__.spl
```

**Phase 2c: Type Checking**

```
src/compiler/feature/type_checking/
  app/
    type_checker.spl
    type_inference.spl
    ports.spl
  __init__.spl
```

**Phase 2d: HIR + MIR Lowering**

```
src/compiler/feature/hir_lowering/
  app/
    hir_lower.spl
    name_resolver.spl
    ports.spl
  __init__.spl

src/compiler/feature/mir_lowering/
  app/
    mir_lower.spl
    cfg_builder.spl
    ports.spl
  __init__.spl
```

**Phase 2e: Codegen + Backends**

```
src/compiler/feature/codegen/
  app/
    driver.spl
    backend_selector.spl
    ports.spl
  backends/
    llvm/  cranelift/  wasm/  native/  cuda/  vulkan/  lean/
  __init__.spl
```

**Deliverables:**
- Each stage has its own module with ports
- Stage tests pass independently (using mock ports)

---

### Phase 3: Transform Dimension — Stage Boundary Adapters

**Goal:** Add explicit transform modules for each major stage boundary.

**Priority order (most complex mismatch first):**

**Phase 3a: `typing_to_hir` (HIGH PRIORITY)**
- Bridges typed AST context into HIR lowering input
- Creates `TypedAstContext` aggregation struct

**Phase 3b: `hir_to_mir` (HIGH PRIORITY)**
- Bridges HIR structured control flow into MIR basic blocks
- Creates `CfgContext` for control flow tracking

**Phase 3c: `mir_to_backend` (HIGH PRIORITY)**
- Bridges MIR program view for backend consumption
- Creates `MirProgram` normalized view

**Phase 3d: `parsing_to_desugaring` (MEDIUM)**
- Bridges raw AST into desugar pipeline input
- Creates `AstDesugarView`

**Phase 3e: `desugaring_to_typing` (MEDIUM)**
- Bridges desugared AST into type checker input

**Phase 3f: `lexing_to_parsing` (LOW — simple)**
- Token stream view (minimal mismatch)

**Deliverables:**
- `src/compiler/transform/` directory with `__init__.spl` configs
- Each transform has: entity_view, `__init__.spl` with arch config
- Stage features updated to import from transform, not from prior stage

---

### Phase 4: Architecture Enforcement

**Goal:** Add arch configs to all `__init__.spl` files. Compiler tool
validates dependency rules.

**File: `src/compiler/feature/hir_lowering/__init__.spl`**

```simple
arch {
  dimension = "feature"
  layer = "app"

  uses_transform = "compiler/transform/feature/typing_to_hir"

  imports {
    allow = [
      "compiler/feature/hir_lowering/**",
      "compiler/transform/feature/typing_to_hir/**",
      "compiler_core/entity/hir/**",
      "shared/**"
    ]
    deny = [
      "compiler_core/entity/ast/**",             # Must use transform view
      "compiler/feature/type_checking/**"  # Stage isolation
    ]
  }
}
```

**Deliverables:**
- All `__init__.spl` files have arch config blocks
- Architecture validator tool (`bin/simple check-arch`)
- Any violations flagged as build errors

---

### Phase 5: Module Loader as Adapter

**Goal:** Apply the same architecture to the module loader/runtime system.

**Current state:**
- Module loader lives in `src/compiler_core/interpreter/module_loader.spl`
- No clear port definition separating "module resolution" from "execution"

**Proposed:**

```
src/compiler/feature/module_loading/
  app/
    resolver.spl        # Module path resolution logic
    loader.spl          # Actual file loading + parsing
    registry.spl        # Loaded module tracking
    ports.spl           # ModuleResolverPort, ModuleStoragePort
  __init__.spl

src/compiler/transform/feature/loading_to_parsing/
  entity_view/
    ModuleView.spl      # Bridges loaded module source → parser input
  __init__.spl

src/compiler/adapters/
  out/
    file_system/
      FileModuleStorage.spl   # Implements ModuleStoragePort (actual disk reads)
    in_memory/
      MemoryModuleStorage.spl # Mock for testing
```

**Deliverables:**
- Module loader as clean feature module
- Ports defined for file system access
- In-memory mock for fast unit tests

---

### Phase 6: Interpreter as Backend

**Goal:** Treat the tree-walk interpreter as just another backend (outbound adapter).

**Current state:**
- Interpreter in `src/compiler_core/interpreter/eval.spl` is tightly coupled with runtime

**Proposed:**

```
src/compiler/feature/codegen/
  backends/
    interpreter/
      backend.spl          # Implements BackendPort (was eval.spl)
      evaluator.spl        # Tree-walk evaluation
      env.spl              # Scope/env management (was env.spl)
      value.spl            # Runtime values (was value.spl)
      ops.spl              # Operations (was ops.spl)
      jit.spl              # JIT dispatch
      __init__.spl
```

**Benefit:** Driver code can select interpreter vs LLVM vs Cranelift through
the same `BackendPort` interface, simplifying the compiler driver.

---

### Phase 7: Pipeline as Event Bus (Future)

**Goal:** Allow plugins / compiler extensions to hook into pipeline events.

**Proposed:**

```simple
# src/compiler/feature/codegen/app/ports.spl

struct CompilationEventPort:
    """
    Extension point: observe compilation pipeline events.
    Used by: IDE language server, profiler, documentation generator.
    """
    on_parse_complete_fn: fn(AstModule)
    on_type_check_complete_fn: fn(TypedAstContext)
    on_hir_complete_fn: fn(HirModule)
    on_mir_complete_fn: fn(MirProgram)
    on_backend_complete_fn: fn(BackendOutput)
```

**Adapters implementing this port:**
- `LanguageServerAdapter` (IDE hover, completion)
- `ProfilerAdapter` (performance analysis)
- `DocCoverageAdapter` (documentation coverage, hooks into AST)
- `LintAdapter` (style/correctness checks)

---

## 7. Key Architectural Decisions

### Decision 1: Seed Compiler Compatibility

**Issue:** `src/compiler_core/` is compiled by the seed C++ compiler, which has
limited Simple support (no generics in structs, no closures).

**Decision:** Entity types in `src/compiler_core/entity/` MUST remain seed-compatible.
This means:
- Arena-based parallel arrays for AST nodes (not generic structs)
- Integer-tagged unions, not enums
- No generic type parameters on structs

**Exception:** Transform types in `src/compiler/transform/` do NOT need to be
seed-compatible (they run only in the interpreter/compiled mode).

### Decision 2: Incremental Migration

**Issue:** Refactoring all 2,649 files at once is too risky.

**Decision:** Use symlink shims for old paths during migration.
Old path → symlink → new path. Remove symlinks after all importers updated.

**Migration tracking:** `doc/report/compiler_mdsoc_migration.md`

### Decision 3: No Struct Leakage Across Transforms

**Issue:** Raw AST indices (`expr_left: i64`) should not appear in HIR lowering logic.

**Decision:** HIR lowering MUST consume `TypedAstContext` (from transform),
not raw `expr_*` parallel arrays. The transform provides the adapter methods.

### Decision 4: Backends as Outbound Adapters Only

**Issue:** Backends currently mix port definition + implementation.

**Decision:** Each backend implements a common `BackendPort`.
Port is defined in `feature/codegen/app/ports.spl` (owned by application).
Backend implementations live in `feature/codegen/backends/` (adapters).

---

## 8. Dimension Dependency Rules for Compiler

### 8.1 Entity Rules

```
compiler_core/entity/** CANNOT import:
  - compiler/feature/**   (no pipeline logic in IR types)
  - compiler/transform/** (no bridge logic in IR types)
  - adapters/**           (no IO in IR types)

compiler_core/entity/** CAN import:
  - compiler_core/entity/**        (IR types can reference other IR types)
  - shared/**             (Result, Option, etc.)
```

### 8.2 Feature (Stage) Rules

```
compiler/feature/STAGE/** CANNOT import:
  - compiler_core/entity/PRIOR_STAGE/**  (use transform instead)
  - compiler/feature/OTHER_STAGE/** (stage isolation)
  - compiler/backend/**         (no backend knowledge in stages)

compiler/feature/STAGE/** CAN import:
  - compiler/transform/feature/PRIOR_STAGE_to_STAGE/** (transform view)
  - compiler_core/entity/THIS_STAGE/**   (own output types are OK)
  - shared/**
```

### 8.3 Transform Rules

```
compiler/transform/feature/A_to_B/** CANNOT import:
  - compiler/feature/**         (prevents cycles)
  - compiler/transform/feature/OTHER/** (single-hop only)

compiler/transform/feature/A_to_B/** CAN import:
  - compiler_core/entity/A/**            (source dimension)
  - compiler_core/entity/B/**            (target dimension)
  - shared/**
```

---

## 9. Test Strategy Aligned with Architecture

### 9.1 Entity Tests (Pure Unit)

```simple
# test/unit/compiler/entity/ast/expr_spec.spl
describe "AST Expression Arena":
    it "allocates integer literal":
        val idx = expr_alloc_int_lit(42)
        expect(expr_tag[idx]).to_equal(EXPR_INT_LIT)
        expect(expr_i_val[idx]).to_equal(42)
```

### 9.2 Stage Tests (Unit with Mock Ports)

```simple
# test/unit/compiler/feature/type_checking/type_checker_spec.spl
describe "Type checker (stage)":
    it "infers integer literal type":
        # Build mock input via transform
        val ctx = TypeCheckerInputPort(
            get_ast_fn: fn(): mock_ast_with_int_lit(),
            get_desugar_output_fn: fn(): DesugarOutput.empty()
        )

        val result = run_type_checking(ctx)

        val types = result.get_typed_ast_fn()
        expect(types.get_expr_type(0).tag).to_equal(HIR_TYPE_I64)
```

### 9.3 Transform Tests (Adapter Contract Tests)

```simple
# test/unit/compiler/transform/typing_to_hir/TypedAstView_spec.spl
describe "TypedAstView transform":
    it "provides expr type lookup":
        val typed_ast = make_typed_ast()
        val view = TypedAstContext.from_typed(typed_ast.ast, typed_ast.types, typed_ast.syms)

        expect(view.get_expr_type(0).tag).to_equal(HIR_TYPE_I64)

    it "resolves names in scope":
        val view = make_view_with_var("x", HIR_TYPE_I64)
        val sym = view.resolve_name("x", 0)
        expect(sym).to_not_be_nil()
        expect(sym.type_idx).to_equal(HIR_TYPE_I64)
```

### 9.4 Pipeline Integration Tests

```simple
# test/integration/compiler/pipeline/
describe "Full compilation pipeline":
    it "compiles hello world":
        val source = 'print "Hello, world!"'
        val result = compile_to_mir(source)
        expect(result.is_ok()).to_equal(true)
        expect(result.unwrap().main_function()).to_not_be_nil()
```

---

## 10. Summary

### What Changes

| Aspect | Before | After |
|--------|--------|-------|
| IR types | Scattered in `src/compiler_core/*.spl` | `src/compiler_core/entity/*/` |
| Stage logic | Mixed in `src/compiler_core/` and `src/compiler/` | `src/compiler/feature/*/` |
| Stage boundaries | Implicit (direct imports) | `src/compiler/transform/feature/*/` |
| Backends | Mixed with driver | `src/compiler/feature/codegen/backends/*/` |
| Interpreter | Standalone in `src/compiler_core/interpreter/` | Backend adapter |
| Test isolation | Hard (shared globals) | Easy (mock ports) |

### What Stays the Same

- All IR data structures (same fields, same behavior)
- Compilation correctness (same output)
- Seed compiler compatibility (core entity types unchanged internally)
- All test assertions

### Phasing

| Phase | Focus | Risk |
|-------|-------|------|
| 1 | Extract IR entity types | Low |
| 2 | Feature modules per stage | Medium |
| 3 | Transform stage boundaries | Medium |
| 4 | Arch enforcement | Low |
| 5 | Module loader as adapter | Medium |
| 6 | Interpreter as backend | High |
| 7 | Event bus (future) | Future |

---

## 11. References

- `doc/research/mdsoc_design.md` — MDSoC dimension system design
- `doc/guide/standard_architecture.md` — Standard Simple architecture
- `doc/guide/dimension_transform_examples.md` — Transform pattern examples
- `doc/guide/transform_init_examples.md` — `__init__.spl` configuration examples
- `src/compiler_core/ast.spl` — Current AST arena (entity source)
- `src/compiler_core/interpreter/eval.spl` — Current interpreter (future backend adapter)
- `src/app/desugar/` — Current desugaring pipeline (future feature stage)
