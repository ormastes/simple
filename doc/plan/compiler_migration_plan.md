# Compiler Migration Plan: Rust → Simple

**Created:** 2026-02-04
**Status:** Planning Phase
**Goal:** Migrate remaining Rust compiler code to Simple (self-hosting)

## Current Status

### Progress Metrics

| Metric | Rust | Simple | Progress |
|--------|------|--------|----------|
| Files | 558 | 224 | 40% |
| Lines | 193,200 | 72,059 | 37% |
| Modules | ~150 | ~60 | 40% |

### What's Already Migrated ✅

**Core Compiler (44,940 lines):**
- type_infer.spl (2141 lines) - Type inference
- parser.spl (1813 lines) - Parser
- treesitter.spl (1444 lines) - Tree-sitter integration
- lexer.spl (1268 lines) - Lexer
- hir_lowering.spl (1205 lines) - HIR lowering
- backend.spl (1147 lines) - Backend
- codegen.spl (1025 lines) - Code generation
- mir_lowering.spl (925 lines) - MIR lowering
- mir_data.spl (862 lines) - MIR data structures
- resolve.spl (851 lines) - Name resolution
- traits.spl (805 lines) - Trait system
- driver.spl (769 lines) - Compiler driver

**Type System:**
- dim_constraints.spl (637 lines) - Dimension constraints
- higher_rank_poly_*.spl (~1700 lines) - Higher-rank polymorphism
- associated_types_*.spl (~1500 lines) - Associated types
- macro_checker_*.spl (~1700 lines) - Macro checking

### What Needs Migration ⏳

**HIGH PRIORITY - Interpreter (~6000 lines):**
1. interpreter_eval.rs (1156 lines) - Expression evaluation
2. interpreter_control.rs (751 lines) - Control flow
3. interpreter_native_net.rs (750 lines) - Network operations
4. interpreter_state.rs (706 lines) - State management
5. interpreter_native_io.rs (631 lines) - I/O operations
6. interpreter_ffi.rs (629 lines) - FFI calls
7. interpreter_contract.rs (621 lines) - Contract checking
8. interpreter_unit.rs (504 lines) - Unit testing
9. interpreter_patterns.rs (443 lines) - Pattern matching

**MEDIUM PRIORITY - Error Handling (~3000 lines):**
1. error.rs (1789 lines) - Error types and codes
2. value_bridge.rs (750 lines) - Value conversion
3. value.rs (674 lines) - Runtime values
4. value_impl.rs (467 lines) - Value implementations
5. value_async.rs (419 lines) - Async values
6. value_pointers.rs (418 lines) - Pointer values

**LOW PRIORITY - Tooling (~2000 lines):**
1. web_compiler.rs (768 lines) - Web compiler
2. mcp.rs (630 lines) - MCP protocol
3. elf_utils.rs (539 lines) - ELF utilities
4. pipeline_parallel.rs (589 lines) - Pipeline parallelism

## Migration Strategy

### Phase 1: Foundation (Weeks 1-2)

**Goal:** Migrate core value and error types

**Tasks:**
1. Create Simple versions of error codes
   - File: `src/compiler/error_codes.spl`
   - Extract error code constants from error.rs
   - ~200 lines

2. Migrate value types
   - File: `src/compiler/value_types.spl`
   - Define RuntimeValue enum
   - Basic value operations
   - ~500 lines

3. Create value conversion layer
   - File: `src/compiler/value_bridge.spl`
   - Rust ↔ Simple value conversion
   - ~400 lines

**Expected Output:**
- 3 new Simple files (~1100 lines)
- Foundation for interpreter migration

### Phase 2: Interpreter Core (Weeks 3-5)

**Goal:** Migrate main interpreter logic

**Tasks:**
1. Migrate interpreter state
   - File: `src/compiler/interpreter/state.spl`
   - Thread-local state management
   - Execution modes
   - ~600 lines (simplified from Rust)

2. Migrate expression evaluator
   - File: `src/compiler/interpreter/eval.spl`
   - Expression evaluation
   - Function calls
   - ~1000 lines

3. Migrate control flow
   - File: `src/compiler/interpreter/control.spl`
   - Loops, conditionals
   - Break/continue/return
   - ~600 lines

4. Migrate pattern matching
   - File: `src/compiler/interpreter/patterns.spl`
   - Pattern destructuring
   - Match expressions
   - ~400 lines

**Expected Output:**
- 4 new Simple files (~2600 lines)
- Core interpreter working

### Phase 3: Native Operations (Weeks 6-7)

**Goal:** Migrate native I/O and FFI

**Tasks:**
1. Migrate I/O operations
   - File: `src/compiler/interpreter/native_io.spl`
   - File operations
   - Network operations
   - ~800 lines

2. Migrate FFI handling
   - File: `src/compiler/interpreter/ffi.spl`
   - External function calls
   - C interop
   - ~500 lines

3. Migrate contracts
   - File: `src/compiler/interpreter/contracts.spl`
   - Pre/post conditions
   - Invariants
   - ~500 lines

**Expected Output:**
- 3 new Simple files (~1800 lines)
- Full interpreter feature set

### Phase 4: Advanced Features (Weeks 8-10)

**Goal:** Migrate remaining features

**Tasks:**
1. Migrate unit testing support
   - File: `src/compiler/interpreter/unit.spl`
   - Test framework integration
   - ~400 lines

2. Migrate async support
   - File: `src/compiler/value/async.spl`
   - Async values
   - Promise handling
   - ~350 lines

3. Migrate pointers
   - File: `src/compiler/value/pointers.spl`
   - Unique pointers
   - Move semantics
   - ~350 lines

**Expected Output:**
- 3 new Simple files (~1100 lines)
- Complete feature parity

### Phase 5: Tooling (Weeks 11-12)

**Goal:** Migrate dev tools

**Tasks:**
1. Migrate web compiler
   - File: `src/compiler/web_compiler.spl`
   - WASM support
   - Web API
   - ~600 lines

2. Migrate MCP protocol
   - File: `src/compiler/mcp.spl`
   - Model Context Protocol
   - ~500 lines

3. Migrate utilities
   - Files: Various utility modules
   - ELF utils, parallel pipeline
   - ~800 lines

**Expected Output:**
- Multiple utility files (~1900 lines)
- Full tooling support

## Migration Timeline

```
Week 1-2:   Phase 1 - Foundation
Week 3-5:   Phase 2 - Interpreter Core
Week 6-7:   Phase 3 - Native Operations
Week 8-10:  Phase 4 - Advanced Features
Week 11-12: Phase 5 - Tooling
```

**Total:** 12 weeks (~3 months)

## Technical Challenges

### Challenge 1: Thread-Local State

**Rust Pattern:**
```rust
thread_local! {
    static STATE: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());
}
```

**Simple Solution:**
```simple
# Use module-level mutable variables
var thread_state: Dict<text, Value> = {}

fn get_state(key: text) -> Value?:
    thread_state.get(key)
```

**Note:** Simple doesn't have thread_local! yet. Will use module globals initially.

### Challenge 2: Atomic Operations

**Rust Pattern:**
```rust
static INTERRUPT: AtomicBool = AtomicBool::new(false);
```

**Simple Solution:**
```simple
# Use extern atomic FFI
extern fn rt_atomic_bool_new(initial: bool) -> i64
extern fn rt_atomic_bool_load(ptr: i64) -> bool

val interrupt_flag = rt_atomic_bool_new(false)
```

**Note:** Use existing atomic FFI from runtime.

### Challenge 3: Value Representation

**Rust Pattern:**
```rust
pub enum Value {
    Int(i64),
    Float(f64),
    String(RuntimeString),
    // ... 20+ variants
}
```

**Simple Solution:**
```simple
enum RuntimeValue:
    Int(i64)
    Float(f64)
    String(text)
    # ... all variants

# Use existing runtime RuntimeValue via FFI
```

**Note:** Reuse runtime's RuntimeValue type via FFI initially.

### Challenge 4: Error Handling

**Rust Pattern:**
```rust
#[derive(Error)]
pub enum CompilerError {
    #[error("Type mismatch: {0}")]
    TypeMismatch(String),
}
```

**Simple Solution:**
```simple
enum CompilerError:
    TypeMismatch(message: text)
    UndefinedVariable(name: text)
    # ... all variants

impl CompilerError:
    fn message() -> text:
        match self:
            TypeMismatch(msg): "Type mismatch: {msg}"
            UndefinedVariable(name): "Undefined variable: {name}"
```

**Note:** Simple has pattern matching and string interpolation.

## Migration Process

### For Each Module:

1. **Read Rust file** - Understand structure and dependencies
2. **Extract types** - Create Simple type definitions
3. **Convert functions** - Translate Rust → Simple
4. **Handle Rust-specific features**:
   - thread_local! → module variables
   - AtomicBool → extern atomic FFI
   - RefCell<T> → mut T
   - Option<T> → T?
   - Result<T, E> → Result<T, E> (native)
5. **Test** - Verify functionality
6. **Document** - Add comments and examples
7. **Update this plan** - Mark as complete

### Conversion Guidelines

**Type Conversions:**
```
Rust                  Simple
----                  ------
String                text
Vec<T>                [T]
HashMap<K, V>         Dict<K, V>
Option<T>             T?
Result<T, E>          Result<T, E>
Box<T>                T (no boxing needed)
Arc<T>                T (GC handles sharing)
RefCell<T>            mut T
```

**Function Signatures:**
```rust
// Rust
pub fn evaluate(expr: &Expr) -> Result<Value, Error>

// Simple
fn evaluate(expr: Expr) -> Result<Value, Error>:
    # No & needed - Simple handles references
```

**Pattern Matching:**
```rust
// Rust
match value {
    Value::Int(n) => n + 1,
    Value::Float(f) => f.ceil() as i64,
    _ => 0,
}

// Simple
match value:
    Int(n): n + 1
    Float(f): f.ceil().to_i64()
    _: 0
```

## Success Criteria

### Phase Completion:
- ✅ All planned files migrated
- ✅ Tests passing
- ✅ Zero Rust compiler files remaining
- ✅ Documentation updated

### Quality Metrics:
- Zero compiler warnings
- All existing tests pass
- Performance within 10% of Rust version
- Code coverage ≥ 80%

## Tracking

### Migration Progress Table

| Phase | Status | Files | Lines | Completion |
|-------|--------|-------|-------|------------|
| Phase 1 | 🔄 In Progress | 1/3 | 250/1100 | 23% |
| Phase 2 | ⏳ Not Started | 0/4 | 0/2600 | 0% |
| Phase 3 | ⏳ Not Started | 0/3 | 0/1800 | 0% |
| Phase 4 | ⏳ Not Started | 0/3 | 0/1100 | 0% |
| Phase 5 | ⏳ Not Started | 0/3 | 0/1900 | 0% |

**Overall:** 1/16 files, 250/8500 lines migrated (3%)

### Weekly Updates

#### Week 1 - Day 1 (2026-02-04)

**Files Migrated:**
- ✅ error_codes.spl (250 lines) - All compiler error codes

**Lines Migrated:** 250 / 8500 (3%)

**Progress:**
- Created error_codes.spl with all error code constants
- Added helper functions for error categorization
- Simpler than Rust version (no module nesting needed)

**Challenges:**
- None yet (straightforward constants migration)

**Next Steps:**
- Continue Phase 1: Migrate value types
- Then value conversion layer

## Resources

### Documentation
- Simple Language Guide: `doc/guide/syntax_quick_reference.md`
- FFI Reference: `/ffi` skill
- Pattern Matching: `doc/design/pattern_matching.md`

### Tools
- Migration script: `script/migrate_rust_to_simple.spl` (to be created)
- Test runner: `simple test`
- Linter: `simple lint`

### Support
- Existing Simple compiler: `src/compiler/`
- Runtime FFI: `rust/runtime/src/value/ffi/`
- Parser: `src/compiler/parser.spl`

## Next Steps

1. **Review and approve this plan**
2. **Set up migration environment**
3. **Create migration scripts/tools**
4. **Begin Phase 1: Foundation**
5. **Weekly check-ins on progress**

---

**Plan Version:** 1.0
**Last Updated:** 2026-02-04
**Owner:** Compiler Team
**Timeline:** 12 weeks (3 months)
