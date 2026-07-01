# Macro Implementation Plan - Complete All Remaining Features

**Created:** 2026-01-04
**Status:** Planning
**Goal:** Complete 100% of macro system implementation

## Current State (98% Complete)

### Working Features
- Built-in macros: println!, print!, vec!, assert!, assert_eq!, assert_unit!, panic!, format!, dbg!, stringify!
- User-defined macros with const/non-const parameters
- Template substitution in emit blocks (`{param}` → value)
- Hygiene system (gensym-based renaming)
- Intro function generation with for-loops
- Inject "Here" execution at callsite
- Contract parsing and validation

### Remaining Features (8 items)

## Implementation Plan

---

## Phase 1: Template Substitution in Intro Contracts

**Priority:** High
**Difficulty:** Medium
**Estimated Scope:** ~100 lines

### Problem
Currently intro contracts use plain strings for function names:
```simple
intro helper: enclosing.module.fn "my_helper"(n: Int) -> Int
```

But template substitution doesn't work:
```simple
intro axes:
  for i in 0..N:
    enclosing.class.fn "{BASE}{i}"(v: Vec[N]) -> Int  # NOT WORKING
```

### Solution
1. Modify `parse_macro_intro_spec` in `src/parser/src/statements/macro_parsing.rs`
2. Parse function names as f-strings instead of plain strings
3. Apply template substitution during contract processing

### Implementation Steps

#### Step 1.1: Update Intro Spec AST
File: `src/parser/src/ast/nodes/definitions.rs`
```rust
pub struct MacroIntroFunctionSpec {
    pub name: FunctionNameExpr,  // Changed from String
    // ...
}

pub enum FunctionNameExpr {
    Literal(String),
    Template(Vec<FStringPart>),  // f-string parts
}
```

#### Step 1.2: Update Parser
File: `src/parser/src/statements/macro_parsing.rs`
- In `parse_macro_intro_spec`, check if function name is f-string or plain string
- Parse f-string parts if template syntax detected

#### Step 1.3: Update Contract Processing
File: `src/compiler/src/macro_contracts.rs`
- In `process_intro_item`, apply template substitution to function names
- Use existing `substitute_template_string` logic

#### Step 1.4: Add Tests
File: `src/driver/tests/interpreter_macros.rs`
```rust
#[test]
fn macro_intro_template_function_name() {
    let code = r#"
macro gen_getters(BASE: Str const, N: Int const) -> (
    intro getters:
        for i in 0..N:
            enclosing.module.fn "{BASE}{i}"() -> Int
):
    emit getters:
        for i in 0..N:
            fn "{BASE}{i}"() -> Int:
                return i

gen_getters!("get_", 3)
main = get_0() + get_1() + get_2()  # 0 + 1 + 2 = 3
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}
```

---

## Phase 2: Inject Head/Tail Execution

**Priority:** High
**Difficulty:** Hard
**Estimated Scope:** ~200 lines

### Problem
"Here" injection works, but Head/Tail don't:
- `inject code: callsite.block.head.stmt` - should inject at block start
- `inject code: callsite.block.tail.stmt` - should inject at block end

### Current Blocker
Macro invocations are expressions, evaluated via `evaluate_expr` which has immutable `&Env`. Block-level injection requires statement-level handling.

### Solution
Handle macro invocations at the statement level in `exec_node`, not just expression level.

### Implementation Steps

#### Step 2.1: Add Statement-Level Macro Detection
File: `src/compiler/src/interpreter.rs`

In `exec_block`, detect if a statement is an expression that is a macro invocation:
```rust
pub(crate) fn exec_block(...) -> Result<Control, CompileError> {
    // Collect pending injections
    let mut head_injections: Vec<Block> = vec![];
    let mut tail_injections: Vec<Block> = vec![];

    for stmt in &block.stmts {
        // Check for macro invocation as statement
        if let Node::Expression(Expr::MacroInvocation { .. }) = stmt {
            // Execute macro and collect injections
            let result = exec_macro_with_injections(stmt, env, ...)?;
            head_injections.extend(result.head);
            tail_injections.extend(result.tail);
        }
        // ... normal execution
    }

    // Execute tail injections before returning
    for block in tail_injections {
        exec_block(&block, env, ...)?;
    }
}
```

#### Step 2.2: Create Injection Collection Helper
File: `src/compiler/src/interpreter_macro.rs`

```rust
pub struct InjectionResult {
    pub value: Value,
    pub head_blocks: Vec<Block>,
    pub tail_blocks: Vec<Block>,
}

pub fn execute_macro_with_injections(...) -> Result<InjectionResult, CompileError> {
    let value = evaluate_macro_invocation(...)?;
    if let Some(contract) = take_macro_introduced_symbols() {
        let head = contract.injections.get(&MacroAnchor::Head).cloned().unwrap_or_default();
        let tail = contract.injections.get(&MacroAnchor::Tail).cloned().unwrap_or_default();
        return Ok(InjectionResult { value, head_blocks: head, tail_blocks: tail });
    }
    Ok(InjectionResult { value, head_blocks: vec![], tail_blocks: vec![] })
}
```

#### Step 2.3: Modify Block Execution
File: `src/compiler/src/interpreter.rs`

Insert head injections at block start, tail injections before block end.

#### Step 2.4: Add Tests
```rust
#[test]
fn macro_inject_head_tail() {
    let code = r#"
let log = []

macro with_logging(v: Int) -> (
    returns result: Int,
    inject setup: callsite.block.head.stmt,
    inject cleanup: callsite.block.tail.stmt
):
    emit setup:
        log.push("start")

    emit cleanup:
        log.push("end")

    emit result:
        v

fn test_fn() -> Int:
    let x = with_logging!(42)
    log.push("middle")
    return x

let result = test_fn()
# log should be ["start", "middle", "end"]
main = if log.len() == 3 and log[0] == "start" and log[2] == "end": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}
```

---

## Phase 3: Field Introduction

**Priority:** Medium
**Difficulty:** Hard
**Estimated Scope:** ~150 lines

### Problem
Cannot introduce fields in classes:
```simple
macro add_id() -> (
    intro id_field: enclosing.class.field "id": Int
):
    emit id_field:
        id: Int = 0
```

### Solution
1. Track class context during macro expansion
2. Add field to class definition before class is finalized

### Implementation Steps

#### Step 3.1: Add Class Context Tracking
File: `src/compiler/src/interpreter_macro.rs`

```rust
thread_local! {
    static CURRENT_CLASS_CONTEXT: RefCell<Option<String>> = RefCell::new(None);
}

pub fn set_class_context(name: Option<String>) {
    CURRENT_CLASS_CONTEXT.with(|cell| *cell.borrow_mut() = name);
}
```

#### Step 3.2: Update Class Parsing
File: `src/compiler/src/interpreter.rs`

When entering class body, set context; when exiting, clear it.

#### Step 3.3: Process Field Intro
File: `src/compiler/src/macro_contracts.rs`

```rust
fn process_intro_field(
    intro: &MacroIntro,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    // Extract field name and type from spec
    // Add to result.introduced_fields
}
```

#### Step 3.4: Register Introduced Fields
File: `src/compiler/src/interpreter.rs`

After macro expansion in class context, add fields to class definition.

---

## Phase 4: Variadic Patterns

**Priority:** Medium
**Difficulty:** Medium
**Estimated Scope:** ~150 lines

### Problem
Cannot accept variable number of arguments:
```simple
macro my_vec(...items) -> (returns result: Array):
    emit result:
        [items...]  # Spread items into array
```

### Solution
1. Add variadic parameter syntax to parser
2. Bind variadic args as array in macro expansion

### Implementation Steps

#### Step 4.1: Update MacroParam AST
File: `src/parser/src/ast/nodes/definitions.rs`

```rust
pub struct MacroParam {
    pub name: String,
    pub ty: Type,
    pub is_const: bool,
    pub is_variadic: bool,  // NEW
}
```

#### Step 4.2: Update Parser
File: `src/parser/src/statements/macro_parsing.rs`

Parse `...name` as variadic parameter.

#### Step 4.3: Update Expansion
File: `src/compiler/src/interpreter_macro.rs`

Collect remaining args into array for variadic param.

---

## Phase 5: Recursive Macro Expansion

**Priority:** Low
**Difficulty:** Medium
**Estimated Scope:** ~100 lines

### Problem
Macros cannot call other macros in emit blocks.

### Solution
1. Allow macro invocations in emit blocks
2. Track expansion depth to prevent infinite recursion
3. Add recursion limit (default: 128)

### Implementation Steps

#### Step 5.1: Add Recursion Tracking
```rust
thread_local! {
    static MACRO_EXPANSION_DEPTH: RefCell<usize> = RefCell::new(0);
}

const MAX_MACRO_DEPTH: usize = 128;
```

#### Step 5.2: Check Depth in Expansion
Before expanding, increment depth. After, decrement. Error if > MAX.

---

## Phase 6: Cross-Module Macro Imports

**Priority:** Low
**Difficulty:** Hard
**Estimated Scope:** ~200 lines

### Problem
Cannot import macros from other modules:
```simple
import utils.macros.my_macro!  # NOT WORKING
```

### Solution
1. Add macro export syntax: `pub macro name(...)`
2. Track macro visibility in module system
3. Resolve macro imports during module loading

### Implementation Steps

#### Step 6.1: Add Macro Visibility
Update `MacroDef` to include visibility field.

#### Step 6.2: Export Macro Registry
Store exported macros in module metadata.

#### Step 6.3: Import Resolution
When importing, check if target is a macro and register it.

---

## Phase 7: Macro Debugging/Tracing

**Priority:** Low
**Difficulty:** Easy
**Estimated Scope:** ~50 lines

### Problem
Hard to debug macro expansions.

### Solution
Add `--macro-trace` flag to show expansion steps.

### Implementation Steps

#### Step 7.1: Add Trace Flag
File: `src/driver/src/main.rs`

```rust
#[arg(long)]
macro_trace: bool,
```

#### Step 7.2: Add Trace Output
File: `src/compiler/src/interpreter_macro.rs`

```rust
if MACRO_TRACE.load(Ordering::Relaxed) {
    eprintln!("[macro] expanding {}!(...)", name);
    eprintln!("[macro] const_bindings: {:?}", const_bindings);
    eprintln!("[macro] result: {:?}", result);
}
```

---

## Phase 8: IDE Integration

**Priority:** Low
**Difficulty:** Medium
**Estimated Scope:** ~200 lines

### Features
1. Autocomplete for introduced symbols
2. Hover tooltips showing expansion
3. Jump-to-definition for macro-introduced symbols

### Implementation
Expose `MacroContractResult` to LSP server for symbol information.

---

## Summary

| Phase | Feature | Priority | Difficulty | Lines |
|-------|---------|----------|------------|-------|
| 1 | Template substitution in intro | High | Medium | ~100 |
| 2 | Inject Head/Tail execution | High | Hard | ~200 |
| 3 | Field introduction | Medium | Hard | ~150 |
| 4 | Variadic patterns | Medium | Medium | ~150 |
| 5 | Recursive expansion | Low | Medium | ~100 |
| 6 | Cross-module imports | Low | Hard | ~200 |
| 7 | Debugging/tracing | Low | Easy | ~50 |
| 8 | IDE integration | Low | Medium | ~200 |

**Total estimated:** ~1150 lines

---

## Execution Order

1. **Phase 1** - Template substitution (completes intro feature)
2. **Phase 2** - Inject Head/Tail (completes inject feature)
3. **Phase 3** - Field introduction (completes all intro types)
4. **Phase 4** - Variadic patterns (common macro need)
5. **Phase 5** - Recursive expansion (enables complex macros)
6. **Phase 7** - Debugging (helps with remaining work)
7. **Phase 6** - Cross-module (needs module system work)
8. **Phase 8** - IDE integration (polish)

---

## Files to Modify

| File | Phases |
|------|--------|
| `src/parser/src/ast/nodes/definitions.rs` | 1, 4 |
| `src/parser/src/statements/macro_parsing.rs` | 1, 4 |
| `src/compiler/src/macro_contracts.rs` | 1, 3 |
| `src/compiler/src/interpreter_macro.rs` | 2, 4, 5, 7 |
| `src/compiler/src/interpreter.rs` | 2, 3 |
| `src/compiler/src/interpreter_eval.rs` | 2 |
| `src/driver/src/main.rs` | 7 |
| `src/driver/tests/interpreter_macros.rs` | All |
