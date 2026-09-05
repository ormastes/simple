# Macro Feature Completion - Technical Analysis

**Date:** 2025-12-27
**Status:** Technical Blocker Identified
**Remaining Work:** Architectural refactoring required (~8-12 hours, not 4-5)

## Executive Summary

The macro contract integration (#1303, #1304) cannot be completed with a simple ~4-5 hour integration as initially estimated. A fundamental architectural constraint prevents symbol table mutation during expression evaluation, requiring either:

1. **Large-scale refactoring** (~8-12 hours): Make symbol tables mutable throughout the interpreter
2. **AST-level preprocessing** (~6-8 hours): Process macros before interpretation begins
3. **Hybrid approach** (~10 hours): Combine both strategies

This document explains the technical blocker, evaluates solutions, and provides a completion roadmap.

## Current Implementation Status

### ✅ What Works (60% Complete)

**Infrastructure (100% functional):**
- `macro_contracts.rs` (390 lines) - Processes `intro`/`inject`/`returns` items
- `macro_validation.rs` (488 lines) - Validates ordering, shadowing, types
- Contract processing called in `expand_user_macro()` (line 181)
- Results stored in thread-local `MACRO_INTRODUCED_SYMBOLS`

**Basic Expansion (100% functional):**
- Built-in macros: `println!`, `vec!`, `assert!`, etc.
- User-defined macros with parameters
- `const_eval:` blocks
- `emit` blocks with template substitution
- Hygiene system (gensym-based)

### 🔄 What's Partial (30% Complete)

**Contract Processing:**
- ✅ Parsing contract syntax
- ✅ Processing contracts to extract symbols
- ✅ Storing results in thread-local
- ❌ **Nobody retrieves or registers the symbols**
- ❌ Introduced symbols not available to subsequent code

### ⏳ What's Missing (10% - Blocked)

**Symbol Registration:**
- Retrieve `MacroContractResult` from thread-local
- Register functions in `functions: HashMap<String, FunctionDef>`
- Register classes in `classes: HashMap<String, ClassDef>`
- Register types, variables in appropriate tables

**Problem:** All symbol tables are **immutable** during interpretation.

## The Architectural Blocker

### Root Cause

The interpreter uses **immutable symbol tables** throughout the execution pipeline:

```rust
// src/compiler/src/interpreter.rs:972
pub(crate) fn exec_node(
    node: &Node,
    env: &mut Env,  // Only env is mutable
    functions: &HashMap<String, FunctionDef>,  // IMMUTABLE
    classes: &HashMap<String, ClassDef>,        // IMMUTABLE
    enums: &Enums,                               // IMMUTABLE
    impl_methods: &ImplMethods,                  // IMMUTABLE
) -> Result<Control, CompileError>
```

**Why immutable?**
1. Symbol tables are built during the first pass (lines 498-619)
2. Execution happens in a second pass with frozen tables
3. This enables:
   - Parallel-safe execution (no data races)
   - Predictable name resolution
   - Simpler reasoning about scope

**Problem for macros:**
- Macros are evaluated during the execution pass (as expressions)
- Cannot modify frozen symbol tables
- Introduced symbols have nowhere to go

### Call Chain Analysis

```
interpret_program()  [main entry]
  ├─ First pass: Build symbol tables (mutable locals)
  │   ├─ Node::Function → functions.insert()  ✅
  │   ├─ Node::Class → classes.insert()       ✅
  │   └─ Node::Macro → macros.insert()        ✅
  │
  └─ Second pass: Execute with frozen tables
      └─ exec_node(node, &mut env, &functions, &classes, ...)
          └─ Node::Expression
              └─ Expr::MacroInvocation
                  └─ evaluate_macro_invocation()
                      └─ expand_user_macro()
                          ├─ process_macro_contract()  ✅ Works
                          ├─ Store in MACRO_INTRODUCED_SYMBOLS  ✅ Works
                          └─ ❌ **Can't register - tables are &HashMap**
```

### Evidence from Code

**File:** `src/compiler/src/interpreter_macro.rs:181-187`
```rust
// Process macro contracts to determine introduced symbols (#1303)
let contract_result = process_macro_contract(...)?;

// Store introduced symbols in thread-local for caller to register
// This is necessary because symbol tables are immutable during evaluation
MACRO_INTRODUCED_SYMBOLS.with(|cell| {
    *cell.borrow_mut() = Some(contract_result);
});
// ❌ No caller ever retrieves or registers these symbols
```

**File:** `src/compiler/src/interpreter.rs:606-610`
```rust
Node::Macro(m) => {
    // ...
    // Process macro contracts to register introduced symbols (#1303)
    // Note: For now, contracts with const params need invocation-time processing
    // But we can process non-parameterized contracts at definition time
    // TODO: Full integration requires invocation-time symbol registration
}
```

**The TODO is acknowledged but not implemented.**

## Attempted Solutions & Why They Don't Work

### Attempt 1: Register at Expression Evaluation ❌

**Idea:** Retrieve symbols after `evaluate_macro_invocation()` returns

**Problem:**
```rust
// src/compiler/src/interpreter_expr.rs:1236-1246
Expr::MacroInvocation { name, args } => {
    let result = evaluate_macro_invocation(
        name, args, env,
        functions,  // ← Immutable reference
        classes,    // ← Immutable reference
        ...
    )?;

    // ❌ Can't do this - need &mut HashMap
    let symbols = take_macro_introduced_symbols();
    functions.insert(...);  // ← Compilation error!
}
```

### Attempt 2: Register at Statement Level ❌

**Idea:** Handle `Node::Expression` containing macro, register symbols there

**Problem:**
```rust
// src/compiler/src/interpreter.rs:1229
Node::Expression(expr) => {
    evaluate_expr(
        expr, env,
        functions,  // ← Still immutable here too!
        classes,
        ...
    )?;
    // ❌ Same problem - can't modify immutable HashMap
}
```

### Attempt 3: Make emit Blocks Define Functions ❌

**Idea:** Have `emit` blocks create `fn` definitions that get registered

**Problem:**
```rust
// Macro with emit block
macro define_func() -> ():
    emit code:
        fn my_func() -> Int:  // ← Defined in local env only
            return 42

// Usage
define_func!()
let x = my_func()  // ← Error: undefined variable: my_func
```

Functions defined in macro emit blocks are scoped to the macro's local environment and don't propagate to the global function table.

## Solution Options

### Option A: Make Symbol Tables Mutable (Recommended)

**Approach:** Change interpreter to use `&mut HashMap` for symbol tables

**Changes Required:**

1. **Update signatures** (~50 functions):
```rust
// Before
pub(crate) fn exec_node(
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
) -> Result<Control, CompileError>

// After
pub(crate) fn exec_node(
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
) -> Result<Control, CompileError>
```

2. **Update all call sites** (~200+ locations):
   - `src/compiler/src/interpreter.rs` - Main interpreter
   - `src/compiler/src/interpreter_expr.rs` - Expression evaluation
   - `src/compiler/src/interpreter_control.rs` - Control flow
   - `src/compiler/src/interpreter_call.rs` - Function calls
   - `src/compiler/src/interpreter_method.rs` - Method calls
   - `src/compiler/src/interpreter_context.rs` - Context blocks
   - `src/compiler/src/interpreter_macro.rs` - Macro expansion
   - `src/compiler/src/interpreter_helpers.rs` - Utilities

3. **Register symbols after macro invocation**:
```rust
// src/compiler/src/interpreter_expr.rs
Expr::MacroInvocation { name, args } => {
    let result = evaluate_macro_invocation(name, args, env, functions, classes, ...)?;

    // Now this works!
    if let Some(symbols) = take_macro_introduced_symbols() {
        for (name, func) in symbols.introduced_functions {
            functions.insert(name, func);
        }
        for (name, class) in symbols.introduced_classes {
            classes.insert(name, class);
        }
        // ... types, vars
    }

    Ok(result)
}
```

**Pros:**
- Clean, proper solution
- Symbols available immediately after macro invocation
- Maintains current architecture
- Enables future dynamic symbol introduction features

**Cons:**
- **Large refactoring**: ~50 function signatures, 200+ call sites
- Potential for introducing bugs in core interpreter
- Breaks parallel safety (would need RefCell or similar)
- **Estimated time**: 8-12 hours

**Risk:** Medium-High (core interpreter changes)

### Option B: AST-Level Macro Preprocessing

**Approach:** Process macros before interpretation, expand to AST nodes

**Changes Required:**

1. **Add preprocessing pass**:
```rust
// src/compiler/src/pipeline.rs
fn preprocess_macros(ast: Vec<Node>) -> Result<Vec<Node>, CompileError> {
    let mut expanded = Vec::new();

    for node in ast {
        match node {
            Node::Expression(Expr::MacroInvocation { ... }) => {
                // Expand macro to AST nodes
                let intro_nodes = expand_macro_to_ast(...)?;
                expanded.extend(intro_nodes);
            }
            _ => expanded.push(node),
        }
    }

    Ok(expanded)
}
```

2. **Create AST generator from contracts**:
```rust
fn contract_to_ast(contract: &MacroContractResult) -> Vec<Node> {
    let mut nodes = Vec::new();

    for (name, func_def) in &contract.introduced_functions {
        nodes.push(Node::Function(func_def.clone()));
    }

    for (name, class_def) in &contract.introduced_classes {
        nodes.push(Node::Class(class_def.clone()));
    }

    nodes
}
```

3. **Update macro expansion** to return AST instead of executing:
```rust
fn expand_macro_to_ast(
    macro_def: &MacroDef,
    args: &[MacroArg],
) -> Result<Vec<Node>, CompileError> {
    let contract_result = process_macro_contract(...)?;
    contract_to_ast(&contract_result)
}
```

**Pros:**
- Macros processed once, before interpretation
- Symbols available when interpretation starts
- No changes to core interpreter
- Cleaner separation of concerns

**Cons:**
- New preprocessing pass adds complexity
- Macros can't depend on runtime values
- Changes macro execution model
- **Estimated time**: 6-8 hours

**Risk:** Medium (new compiler pass)

### Option C: Hybrid Approach

**Approach:** Combine both - preprocess where possible, runtime registration for dynamic cases

1. **Preprocess** macros with const-only parameters
2. **Runtime** register symbols for macros with runtime dependencies
3. Use **RefCell** for interior mutability of symbol tables

**Estimated time**: 10 hours
**Risk:** High (complex, error-prone)

## Recommended Path Forward

### Immediate (Document Current Status)

Update documentation to clearly state the architectural blocker:

**doc/status/macros.md:**
```markdown
## Current Limitation: Symbol Registration Blocked

The infrastructure for macro contract processing is complete (100%), but
symbol registration cannot be implemented without architectural changes
to the interpreter. The blocker is:

- Symbol tables (functions, classes) are immutable during execution
- Macros are evaluated during execution (expression evaluation)
- Cannot modify immutable hash maps to register introduced symbols

**Solutions under consideration:**
1. Make symbol tables mutable (~8-12 hours)
2. AST-level preprocessing (~6-8 hours)
3. Hybrid approach (~10 hours)

**Current workaround:** None - feature requires architectural decision
**Estimated completion**: 8-12 hours after architecture decision made
```

### Short-term (Pick a solution)

**Recommendation: Option A (Mutable Tables)**

**Rationale:**
- Most aligned with current architecture
- Enables future dynamic features
- Clean separation of concerns
- Well-understood changes

**Implementation plan:**
1. Week 1: Update core interpreter signatures (2 days)
2. Week 1: Update all call sites (2 days)
3. Week 1: Add symbol registration logic (1 day)
4. Week 2: Testing and bug fixes (3 days)
5. Week 2: Documentation and examples (2 days)

**Total: 10 working days (8-12 hours focused work)**

### Long-term (Future improvements)

After basic symbol registration works:
1. Implement code injection (`inject` contracts)
2. LL(1) parser integration
3. IDE protocol support
4. Cross-module macro imports

## Test Case

**What should work after completion:**

```simple
macro gen_getter(name: Str const, value: Int const) -> (
    intro getter:
        enclosing.class.fn "{name}"() -> Int
):
    emit getter:
        fn "{name}"() -> Int:
            return value

class Example:
    gen_getter!("get_answer", 42)

    fn test(self):
        self.get_answer()  # ← Should autocomplete and work!

let e = Example()
assert_eq!(e.get_answer(), 42)  # ← Should pass
```

**Currently:** `error: undefined variable: get_answer`
**After completion:** ✅ Works

## Conclusion

The macro contract feature (#1303, #1304) has complete infrastructure but is **architecturally blocked** from completion. The initial 4-5 hour estimate was based on the assumption that symbol tables were mutable.

**Actual completion requires:**
- Architectural decision on solution approach
- 8-12 hours of focused implementation work
- Comprehensive testing of core interpreter changes

**Current accurate status:**
- Infrastructure: 100% complete
- Integration: 0% (blocked by architecture)
- Overall: 60% (infrastructure exists but can't be used)

---

**Analysis by:** Claude Sonnet 4.5
**Date:** 2025-12-27
**Recommendation:** Option A (Mutable Symbol Tables)
**Estimated completion:** 8-12 hours after approval
