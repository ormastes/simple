# Compiler MDSoC: Implementation Plan

> Concrete step-by-step plan to refactor the Simple compiler pipeline
> to use the standard Simple MDSoC architecture.
>
> Design: `doc/research/compiler_mdsoc_design.md`

**Date:** 2026-02-17 (Updated 2026-03-02)
**Status:** Architecture complete, 288/288 tests passing

**Implementation Reality (2026-03-02):**
- All code lives under `src/compiler/85.mdsoc/` (NOT `src/compiler_core/entity/` or `src/compiler/feature/` as planned)
- Phase 1 (Entity Dimension): **NOT DONE** — `src/compiler_core/` does not exist; IR types remain in numbered layers (10.frontend, 20.hir, 30.types, 50.mir, etc.)
- Phases 2-7 (Feature/Transform/Adapters): Code written under `85.mdsoc/`, not separate directories
- One-struct-per-file refactor completed — all multi-struct files split (118 source files)
- Compiler uses 17 numbered layers: 00.common, 10.frontend, 15.blocks, 20.hir, 25.traits, 30.types, 35.semantics, 40.mono, 50.mir, 55.borrow, 60.mir_opt, 70.backend, 80.driver, 85.mdsoc, 90.tools, 95.interp, 99.loader
- 8 convenience symlinks (common, frontend, mir, backend, driver, mdsoc, interp, loader) point to numbered dirs
- Old unnumbered dirs (core/, linker/) deleted; contents migrated to numbered layers
- Symlink `src/compiler/mdsoc` -> `85.mdsoc` works around numbered-dir resolution bug
- Tests: **288/288 passing** (0 failures)
- See `doc/report/compiler_mdsoc_migration.md` for current status

---

## Guiding Constraints

1. **Zero regressions** — All 4,067 tests must pass after each phase.
2. **Seed compatibility** — `src/compiler_core/entity/` types must remain seed-compilable.
3. **Incremental** — Symlink shims keep old paths alive during migration.
4. **Smallest delta** — One phase = one PR/commit; each individually reversible.

---

## Phase 1: Entity Dimension — Extract IR Types

**Goal:** Create `src/compiler_core/entity/` as the stable domain of the compiler.
No logic changes — pure file reorganization.

### 1a. Token Entity

**Files to create:**

```
src/compiler_core/entity/
  token/
    __init__.spl
    kinds.spl      ← content from src/compiler_core/tokens.spl (constants only)
    stream.spl     ← content from src/compiler_core/lexer_struct.spl (state struct)
  __init__.spl
```

**`src/compiler_core/entity/token/__init__.spl`:**

```simple
arch {
  dimension = "entity"
  layer = "entity"
  imports {
    allow = ["compiler_core/entity/**", "shared/**"]
    deny  = ["compiler/**", "feature/**"]
  }
  exports {
    expose = ["./kinds", "./stream"]
  }
}
export ./kinds.*
export ./stream.*
```

**Migration steps:**
1. Create `src/compiler_core/entity/token/kinds.spl` — copy token constants from `tokens.spl`
2. Create `src/compiler_core/entity/token/stream.spl` — copy lexer structs from `lexer_struct.spl`
3. Create `__init__.spl` configs
4. Add symlinks: `src/compiler_core/tokens.spl → entity/token/kinds.spl`
5. Run tests — must pass

### 1b. AST Entity

**Files to create:**

```
src/compiler_core/entity/
  ast/
    __init__.spl
    arena.spl      ← parallel-array arenas from src/compiler_core/ast.spl
    nodes.spl      ← CoreExpr/CoreStmt/CoreDecl from src/compiler_core/ast_types.spl
    tags.spl       ← EXPR_*/STMT_*/DECL_* constants
```

**`src/compiler_core/entity/ast/__init__.spl`:**

```simple
arch {
  dimension = "entity"
  layer = "entity"
  imports {
    allow = ["compiler_core/entity/**", "shared/**"]
    deny  = ["compiler/**", "feature/**"]
  }
  exports {
    expose = ["./arena", "./nodes", "./tags"]
  }
}
```

### 1c. HIR Entity

```
src/compiler_core/entity/
  hir/
    __init__.spl
    types.spl      ← CoreHirType + HIR_TYPE_* from src/compiler_core/hir_types.spl
    symbol_table.spl ← CoreSymbolTable/Entry from src/compiler_core/hir_types.spl
```

### 1d. MIR Entity

```
src/compiler_core/entity/
  mir/
    __init__.spl
    inst.spl       ← CoreMirInst + MIR_* from src/compiler_core/mir_types.spl
    block.spl      ← CoreBasicBlock
    func.spl       ← CoreMirFunction
```

### 1e. Type System Entity

```
src/compiler_core/entity/
  types/
    __init__.spl
    core_types.spl ← TYPE_* constants from src/compiler_core/types.spl
    generic.spl    ← Generic type representation
```

### Phase 1 Acceptance Criteria

**Status: NOT DONE** — `src/compiler_core/` does not exist. Entity types remain in their numbered compiler layers. This phase was deferred in favor of implementing the MDSOC engine, feature ports, and transforms under `85.mdsoc/`.

- [ ] `src/compiler_core/entity/` exists with all subdirectories
- [ ] All `__init__.spl` files have arch configs
- [ ] Old paths still work via symlinks
- [ ] `bin/simple test` — all tests passing

---

## Phase 2: Feature Dimension — Pipeline Stage Modules

**Goal:** Give each pipeline stage a clean feature module with ports.
Isolates stages from each other.

### 2a. Lexing Stage

**Files to create:**

```
src/compiler/feature/lexing/
  app/
    lexer.spl          ← thin wrapper/delegate to compiler_core/lexer.spl
    ports.spl          ← LexerInputPort, LexerOutputPort
  __init__.spl
```

**`src/compiler/feature/lexing/app/ports.spl`:**

```simple
"""
Ports for the lexing stage.
Lexer neither reads files itself nor knows about modules.
"""

struct LexerInputPort:
    """Source text provider."""
    get_source_fn: fn() -> text

struct LexerOutputPort:
    """Token stream consumer."""
    token_tags: [i64]
    token_texts: [text]
    token_lines: [i64]
    token_cols: [i64]
    token_count: i64
```

**`src/compiler/feature/lexing/__init__.spl`:**

```simple
arch {
  dimension = "feature"
  layer = "app"

  imports {
    allow = [
      "compiler_core/entity/token/**",    # Own output type
      "shared/**"
    ]
    deny = [
      "compiler/feature/parsing/**",    # Stage isolation
      "compiler/feature/desugaring/**",
      "compiler_core/entity/ast/**"              # Don't skip ahead
    ]
  }

  exports {
    expose = ["./app/lexer", "./app/ports"]
  }
}
```

### 2b. Parsing Stage

**Files to create:**

```
src/compiler/feature/parsing/
  app/
    parser.spl         ← delegate to src/compiler_core/parser.spl
    ports.spl          ← ParserInputPort, ParserOutputPort
  __init__.spl
```

**`src/compiler/feature/parsing/app/ports.spl`:**

```simple
struct ParserInputPort:
    """Token stream from lexer."""
    token_tags: [i64]
    token_texts: [text]
    token_count: i64

struct ParserOutputPort:
    """Parsed AST module."""
    # Arena outputs (parallel arrays from parser)
    expr_count: i64
    stmt_count: i64
    decl_count: i64
    root_decls: [i64]
    errors: [ParseError]

struct ParseError:
    message: text
    line: i64
    col: i64
```

### 2c. Desugaring Stage

**Move from `src/app/desugar/` → `src/compiler/feature/desugaring/`**

```
src/compiler/feature/desugaring/
  app/
    mod.spl            ← pipeline orchestrator
    forwarding.spl     ← pass 0
    static_constants.spl  ← pass 1
    static_methods.spl    ← pass 2
    enum_constructors.spl ← pass 3
    rewriter.spl          ← pass 4
    ports.spl
  __init__.spl
```

**`src/compiler/feature/desugaring/app/ports.spl`:**

```simple
struct DesugarInputPort:
    """Source text + AST module (desugar works at source level)."""
    source_text_fn: fn() -> text
    ast_module_fn: fn() -> ParserOutputPort

struct DesugarOutputPort:
    """Desugared source + rewritten AST."""
    desugared_source: text
    # Same AST shape, rewrites applied
    modified_decls: [i64]
```

### 2d. Type Checking Stage

```
src/compiler/feature/type_checking/
  app/
    type_checker.spl
    type_inference.spl
    ports.spl
  __init__.spl
```

**`src/compiler/feature/type_checking/app/ports.spl`:**

```simple
struct TypeCheckInputPort:
    """Input from desugaring."""
    get_ast_fn: fn() -> ParserOutputPort
    get_desugar_output_fn: fn() -> DesugarOutputPort

struct TypeCheckOutputPort:
    """Typed AST context."""
    inferred_types: [i64]     # Per-expr type index
    symbol_table: CoreSymbolTable
    diagnostics: [Diagnostic]
    error_count: i64

struct Diagnostic:
    severity: text   # "error", "warning", "info"
    message: text
    line: i64
    col: i64
    span_end_line: i64
    span_end_col: i64
```

### 2e. HIR Lowering Stage

```
src/compiler/feature/hir_lowering/
  app/
    hir_lower.spl
    name_resolver.spl
    implicit_return.spl
    ports.spl
  __init__.spl
```

**`src/compiler/feature/hir_lowering/app/ports.spl`:**

```simple
struct HirLowerInputPort:
    """Typed AST context from transform (NOT direct from type_checking)."""
    # Provided by typing_to_hir transform view
    get_context_fn: fn() -> TypedAstContext

struct HirLowerOutputPort:
    """HIR module."""
    functions: [HirFunction]
    structs: [HirStruct]
    error_count: i64
```

### 2f. MIR Lowering Stage

```
src/compiler/feature/mir_lowering/
  app/
    mir_lower.spl
    cfg_builder.spl
    bb_builder.spl
    ports.spl
  __init__.spl
```

**`src/compiler/feature/mir_lowering/app/ports.spl`:**

```simple
struct MirLowerInputPort:
    """HIR module from transform (NOT direct from hir_lowering)."""
    get_hir_fn: fn() -> HirView  # From transform, not raw HIR

struct MirLowerOutputPort:
    """MIR program."""
    functions: [CoreMirFunction]
    extern_fns: [text]
    string_literals: [text]
```

### 2g. Codegen Stage

```
src/compiler/feature/codegen/
  app/
    driver.spl
    backend_selector.spl
    ports.spl
  backends/
    llvm/backend.spl
    cranelift/backend.spl
    wasm/backend.spl
    native/backend.spl
    interpreter/backend.spl   ← interpreter as just another backend
    cuda/backend.spl
    vulkan/backend.spl
    lean/backend.spl
  __init__.spl
```

**`src/compiler/feature/codegen/app/ports.spl`:**

```simple
struct BackendPort:
    """Common interface all backends implement."""
    target_triple: text
    compile_fn: fn(MirProgram) -> Result
    get_object_bytes_fn: fn() -> [i64]

struct CodegenInputPort:
    """MIR program from transform (NOT direct from mir_lowering)."""
    get_mir_fn: fn() -> MirProgram  # From transform

struct CodegenOutputPort:
    """Backend output for linker."""
    object_bytes: [i64]
    symbol_map: dict
    target_triple: text
```

### Phase 2 Acceptance Criteria

**Status: DONE** — Implemented under `src/compiler/85.mdsoc/feature/` (12 stages, 46 files, one-struct-per-file). Location differs from plan (`85.mdsoc/feature/` not `src/compiler/feature/`).

- [x] Each stage in `src/compiler/85.mdsoc/feature/*/`
- [x] Each stage has port struct files with input/output ports
- [x] Each stage has `__init__.spl` with arch config
- [x] Stage isolation via arch configs
- [x] All tests passing (288/288 MDSOC tests)

---

## Phase 3: Transform Dimension — Stage Boundaries

**Goal:** Add explicit transform modules for each major stage boundary.
No stage logic in transforms — only adaptation.

### 3a. `typing_to_hir` (HIGHEST PRIORITY)

**File: `src/compiler/transform/feature/typing_to_hir/entity_view/TypedAstView.spl`**

See Section 4.1 of `compiler_mdsoc_design.md` for full implementation.

**`src/compiler/transform/feature/typing_to_hir/__init__.spl`:**

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "feature/type_checking"
    to   = "feature/hir_lowering"
    allow_from = [
      "compiler_core/entity/ast/**",
      "compiler_core/entity/types/**",
      "compiler_core/entity/hir/**"
    ]
  }

  imports {
    allow = [
      "compiler_core/entity/ast/**",
      "compiler_core/entity/types/**",
      "compiler_core/entity/hir/**",
      "shared/**"
    ]
    deny = [
      "compiler/feature/**"  # No cycles
    ]
  }

  exports {
    expose = ["./entity_view/TypedAstView"]
  }
}
```

### 3b. `hir_to_mir`

**File: `src/compiler/transform/feature/hir_to_mir/entity_view/HirView.spl`**

See Section 4.2 of design doc for full implementation.

**`src/compiler/transform/feature/hir_to_mir/__init__.spl`:**

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "feature/hir_lowering"
    to   = "feature/mir_lowering"
    allow_from = [
      "compiler_core/entity/hir/**",
      "compiler_core/entity/mir/**"
    ]
  }

  imports {
    allow = [
      "compiler_core/entity/hir/**",
      "compiler_core/entity/mir/**",
      "shared/**"
    ]
    deny = ["compiler/feature/**"]
  }
}
```

### 3c. `mir_to_backend`

**File: `src/compiler/transform/feature/mir_to_backend/entity_view/MirView.spl`**

See Section 4.3 of design doc for full implementation.

```simple
arch {
  dimension = "transform"
  layer = "none"

  transform {
    from = "feature/mir_lowering"
    to   = "feature/codegen"
    allow_from = ["compiler_core/entity/mir/**"]
  }

  imports {
    allow = ["compiler_core/entity/mir/**", "shared/**"]
    deny  = ["compiler/feature/**"]
  }
}
```

### 3d. `parsing_to_desugaring`

```
src/compiler/transform/feature/parsing_to_desugaring/
  entity_view/
    __init__.spl
    AstDesugarView.spl
  __init__.spl
```

**`AstDesugarView.spl`** bridges the raw AST output to desugar's source-text-first model:

```simple
reexport compiler_core/entity/ast/arena.*
reexport compiler_core/entity/ast/tags.*

struct AstDesugarView:
    """
    Combines source text + AST for desugar pipeline.
    Desugar currently works on source text; this bridges both.
    """
    source_text: text
    ast_root_decls: [i64]
    decl_count: i64

    fn source_for_decl(decl_idx: i64) -> text:
        """Extract source text for a declaration (using span info)."""
        val line_start = decl_span[decl_idx * 2]
        val line_end = decl_span[decl_idx * 2 + 1]
        extract_lines(self.source_text, line_start, line_end)
```

### 3e. `desugaring_to_typing`

```
src/compiler/transform/feature/desugaring_to_typing/
  entity_view/
    __init__.spl
    DesugarTypingView.spl
  __init__.spl
```

```simple
struct DesugarTypingView:
    """
    Provides typing stage with what it needs from desugaring.
    Hides desugar pipeline internals.
    """
    desugared_source: text
    root_decls: [i64]
    injected_fns: [text]   # New function names generated by desugar

    fn all_declarations() -> [i64]:
        """Combined original + injected declarations."""
        self.root_decls
```

### Phase 3 Acceptance Criteria

**Status: DONE** — Implemented under `src/compiler/85.mdsoc/transform/` (9 boundaries, 21 files). Location differs from plan (`85.mdsoc/transform/` not `src/compiler/transform/`).

- [x] `src/compiler/85.mdsoc/transform/` exists with `__init__.spl`
- [x] 9 transform modules created (all boundaries)
- [x] Each transform: entity_view + `__init__.spl` with arch config
- [x] All tests passing (288/288 MDSOC tests)

---

## Phase 4: Architecture Enforcement

**Goal:** Add build-time verification of dimension rules.

### 4a. Arch Config Validator

Create `src/app/cli/arch_check.spl`:

```simple
"""
@tag:api
Validate architecture rules from __init__.spl arch{} configs.
Usage: bin/simple check-arch [path]
"""

fn check_architecture(root_dir: text) -> Result:
    val configs = collect_arch_configs(root_dir)
    var violations = []

    for config in configs:
        val module_violations = check_module(config, configs)
        for v in module_violations:
            violations.append(v)

    if violations.len() > 0:
        return Result.error(format_violations(violations))

    Result.ok("Architecture check passed")

fn check_module(config: ArchConfig, all_configs: [ArchConfig]) -> [text]:
    var violations = []
    # Check each import against allow/deny lists
    for import_path in config.actual_imports:
        if is_denied(import_path, config.deny_patterns):
            violations.append(
                "ARCH VIOLATION: {config.module_path} imports {import_path}\n" +
                "  Rule: denied by {config.module_path}/__init__.spl"
            )
    violations
```

### 4b. CLI Integration

Add `check-arch` to CLI dispatch table.

```simple
# src/app/cli/main.spl
# add to COMMAND_TABLE:
CommandEntry(
    name: "check-arch",
    handler: arch_check.run,
    description: "Validate architecture dependency rules"
)
```

### Phase 4 Acceptance Criteria

**Status: DONE** — `src/app/cli/arch_check.spl` implements `check-arch` CLI command.

- [x] `bin/simple check-arch` command exists
- [x] Detects forbidden imports
- [ ] Integrated into `bin/simple build check` (not yet wired)
- [ ] CI script runs arch check (not yet wired)

---

## Phase 5: Module Loader as Adapter (Medium Risk)

**Goal:** Module loader behind a port — enables testing without disk.

### 5a. Define Module Ports

```
src/compiler/feature/module_loading/app/ports.spl
```

```simple
struct ModuleResolverPort:
    """Module path resolution (not file reading)."""
    resolve_fn: fn(text, text) -> text?  # (module_name, context_dir) → abs_path

struct ModuleStoragePort:
    """File reading (swappable in tests)."""
    read_source_fn: fn(text) -> text?  # path → source text

struct ModuleRegistryPort:
    """Loaded module tracking."""
    is_loaded_fn: fn(text) -> bool
    register_fn: fn(text, [text])  # (path, exports)
    get_exports_fn: fn(text) -> [text]
```

### 5b. Implement Adapters

```
src/compiler/adapters/out/
  file_module_storage.spl    # Reads actual files from disk
  memory_module_storage.spl  # In-memory mock for tests
```

### Phase 5 Acceptance Criteria

**Status: DONE** — Ports and adapters in `85.mdsoc/feature/module_loading/` and `85.mdsoc/adapters/out/`.

- [x] Module loader has port interfaces
- [x] `FileModuleStorage` adapter (production)
- [x] `MemoryModuleStorage` adapter (tests)
- [ ] Module tests run without disk access (not yet validated)

---

## Phase 6: Interpreter as Backend Adapter (High Risk)

**Goal:** Interpreter implements `BackendPort`. Same interface as LLVM/Cranelift.

**Risk:** Interpreter is deeply embedded; refactoring carefully.

### 6a. Extract Interpreter Backend

```
src/compiler/feature/codegen/backends/interpreter/
  backend.spl      ← implements BackendPort
  evaluator.spl    ← tree-walk eval (from src/compiler_core/interpreter/eval.spl)
  env.spl          ← scope management
  value.spl        ← runtime values
  ops.spl          ← operations
  jit.spl          ← JIT threshold tracking
  __init__.spl
```

**`backend.spl`:**

```simple
fn create_interpreter_backend() -> BackendPort:
    BackendPort(
        target_triple: "interpreter-simple-runtime",
        compile_fn: fn(mir_program): interpret_mir(mir_program),
        get_object_bytes_fn: fn(): []  # Interpreter has no object output
    )

fn interpret_mir(program: MirProgram) -> Result:
    val evaluator = create_evaluator()
    evaluator.run_main(program.main_function())
```

### Phase 6 Acceptance Criteria

**Status: DONE** — `85.mdsoc/feature/codegen/backends/interpreter/backend.spl` implements BackendPort.

- [x] Interpreter implements `BackendPort`
- [ ] Driver selects interpreter via same `BackendPort` as LLVM (port defined but not wired into real pipeline)
- [x] All tests passing
- [x] Interpreter-specific tests still work

---

## Phase 7: Event Bus for Extensions (Future)

**Deferred** — Implement after phases 1–6 stabilize.

Design in `compiler_mdsoc_design.md` Section 7.

---

## Migration Tracking

Status as of 2026-03-02 (all under `src/compiler/85.mdsoc/`, 118 files):

| Phase | Status | Location | Notes |
|-------|--------|----------|-------|
| 1a-1e: entity | NOT DONE | (planned: src/compiler_core/entity/) | Never extracted; `src/compiler_core/` does not exist |
| 2a-2j: features | DONE | 85.mdsoc/feature/ (12 stages, 46 files) | One-struct-per-file |
| 3a-3f+: transforms | DONE | 85.mdsoc/transform/ (9 boundaries, 21 files) | Entity views |
| 4: arch enforce | DONE | src/app/cli/arch_check.spl | check-arch command |
| 5: module loader | DONE | 85.mdsoc/feature/module_loading/ | Ports + adapters |
| 6: interp backend | DONE | 85.mdsoc/feature/codegen/backends/interpreter/ | BackendPort |
| 7: event bus | DONE | 85.mdsoc/feature/events/ + adapters/in/ | Ports + adapters |
| One-struct refactor | DONE | All files under 85.mdsoc/ | 288/288 tests pass |
| Symlink workaround | DONE | src/compiler/mdsoc -> 85.mdsoc | Bypasses runtime bug |
| Old dirs cleanup | DONE | core/, linker/ deleted/emptied | Contents migrated to numbered layers |

**Compiler Layer Structure (17 numbered layers):**
00.common, 10.frontend, 15.blocks, 20.hir, 25.traits, 30.types, 35.semantics, 40.mono, 50.mir, 55.borrow, 60.mir_opt, 70.backend, 80.driver, 85.mdsoc, 90.tools, 95.interp, 99.loader

See `doc/report/compiler_mdsoc_migration.md` for detailed current status.

---

## Risk Register

| Risk | Mitigation |
|------|-----------|
| Seed compiler breaks after entity move | Keep symlinks; only add new files in Phase 1 |
| Circular imports discovered | Fix before merging; arch check gate |
| Stage isolation breaks desugaring (source-text model) | Keep source-text path in desugar transform |
| Interpreter eval.spl has global state | Module-level vars; move to struct in Phase 6 |
| 2,649 import paths to update | Symlinks first; batch update with `bin/simple fix --dry-run` |
| Test count drops | Rollback; investigate before proceeding |
