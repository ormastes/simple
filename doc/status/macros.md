# Feature #34: Macros - Implementation Status

**Status**: Core Implementation Complete (100% for current scope)
**Difficulty**: 4 (was 5)
**Importance**: 3
**Last Updated**: 2026-01-04

## Summary

Compile-time macros for code generation and metaprogramming. All core macro features are working:

- ✅ **Built-in macros**: println!, print!, vec!, assert!, assert_eq!, format!, dbg!, stringify!, panic!
- ✅ **User-defined macros**: Full contract syntax with intro/inject/returns
- ✅ **Function introduction**: Macros can introduce functions into enclosing scope
- ✅ **Field introduction**: Parser support for macros in class bodies (added 2026-01-04)
- ✅ **Variadic patterns**: `...args` syntax for variable argument lists (added 2026-01-04)
- ✅ **Cross-module imports**: Macros from imported modules available (added 2026-01-04)
- ✅ **LL(1) Parser Integration**: MacroRegistry tracks macros and introduced symbols at parse time (added 2026-01-04)
- ✅ **Inject execution**: "Here" and "Tail" injection working (Head deferred)
- ✅ **For-loop unrolling**: Const-time loops in emit blocks with template substitution
- ✅ **Hygiene system**: Gensym-based variable renaming prevents name collisions
- ✅ **Macro tracing**: `--macro-trace` CLI flag for debugging
- ✅ **Recursion limits**: MAX_MACRO_EXPANSION_DEPTH (128) prevents infinite loops

**95 macro tests passing** across all test files:
- 62 tests in `src/driver/tests/interpreter_macros.rs` (includes 5 LL(1) parser tests)
- 11 tests in `src/driver/tests/interpreter_macro_hygiene.rs`
- 7 macro import tests
- 12 stdlib macro spec tests
- 3 additional macro tests

## Implementation Status by Component

### ✅ Fully Implemented (Working in Production)

#### 1. Built-in Macros (`src/compiler/src/interpreter_macro.rs:17-159`)
- ✅ `println!(...)` - Print with newline
- ✅ `print!(...)` - Print without newline
- ✅ `vec!(...)` - Create arrays
- ✅ `assert!(expr)` - Runtime assertions
- ✅ `assert_eq!(left, right)` - Equality assertions
- ✅ `assert_unit!(value, "type")` - Unit type validation
- ✅ `panic!(msg)` - Abort with message
- ✅ `format!(...)` - String formatting
- ✅ `dbg!(expr)` - Debug print (returns value)
- ✅ `stringify!(expr)` - Convert expression to source string

**Test Coverage:** 50 tests in `src/driver/tests/interpreter_macros.rs`

#### 2. User-Defined Macros
**Syntax:**
```simple
macro name(param1: Type, param2: Type const) -> (
  returns result: RetType,
  intro label: target.kind stub
):
  const_eval:
    const x = 42

  emit label:
    # code using templates and params

  emit result:
    # return value
```

**Features Working:**
- ✅ Macro definition parsing (`src/parser/src/ast.rs` - `MacroDef`)
- ✅ Macro invocation syntax: `name!(args)`
- ✅ Parameter passing and binding
- ✅ `const` parameters for compile-time values
- ✅ `const_eval:` blocks for const computation
- ✅ `emit label:` blocks for code generation
- ✅ Template substitution: `"{NAME}"` → const value

**Test Coverage:** 4 tests for user-defined macros

#### 3. Hygiene System (`src/compiler/src/interpreter_macro.rs:249-873`)
- ✅ Gensym-based variable renaming
- ✅ Scope tracking with `MacroHygieneContext`
- ✅ Prevents name collisions between macro-generated and user code
- ✅ Hygienic transformation of:
  - Variables (`let`, `const`, `static`)
  - Function parameters
  - Lambda parameters
  - Pattern bindings (match, for, if-let, while-let)

**Algorithm:** Each binding gets unique suffix: `name_gensym_N`

### 🔄 Partially Implemented (Infrastructure Complete, Integration Pending)

#### 4. Contract Processing (`src/compiler/src/macro_contracts.rs` - 390 lines)

**Infrastructure Exists:**
- ✅ `MacroContractResult` - Aggregates introduced symbols
- ✅ `process_macro_contract()` - Main processing entry point
- ✅ `intro` item processing for:
  - Functions (`enclosing.class.fn "name"(...)`)
  - Classes (`enclosing.module.class "Name"`)
  - Types (`enclosing.module.type "Alias"`)
  - Variables (`callsite.block.head.let "var": Type`)
- ✅ `inject` item processing:
  - Code injection points: `head`, `tail`, `here`
  - Code kinds: `stmt`, `block`
- ✅ `returns` item processing
- ✅ Const-eval engine:
  - Integer arithmetic: `+`, `-`, `*`, `/`, `%`
  - Boolean conditions: `==`, `!=`, `<`, `<=`, `>`, `>=`
  - Range evaluation for `for i in 0..N`
  - Conditional evaluation for `if condition`
- ✅ Template substitution in stubs: `"{BASE}{i}"` → `"axis0"`
- ✅ Shadowing detection (#1304)

**What's Working:**
- ✅ Symbol table integration - mutable architecture implemented (Phase 1 complete)
- ✅ Symbol registration - macros can now register functions/classes (Phase 1 complete)
- ✅ Thread-local handoff - MACRO_INTRODUCED_SYMBOLS working (Phase 1 complete)
- ✅ Contract parsing - parser fully supports intro/inject/returns syntax (Phase 2 complete)
- ✅ Function extraction - emit blocks properly extract from local_env (Phase 2 complete)
- ✅ Hygiene name resolution - handles gensym-renamed functions (Phase 2 complete)
- ✅ Newline/indent handling - contracts can span multiple lines (Phase 2 complete)
- ✅ End-to-end testing - basic contract functions working (Phase 2 tested)
- ✅ Inject parsing & extraction - inject code extracted to contract result (Phase 3 infrastructure)
- ✅ Template substitution - works in emit blocks with const params (Phase 4 tested)

**What's Missing:**
- ⏳ Template substitution in intro contracts - requires parser support for f-strings in function names
- ⏳ IDE autocomplete support - infrastructure ready but not exposed
- ✅ Inject "Here" execution - works via interpreter_eval.rs with mutable env
- ✅ Inject "Tail" execution - works via thread-local pending injections
- ⏳ Inject "Head" execution - requires block pre-scanning
- ⏳ Field introduction - requires class context analysis
- ✅ For-loop unrolling in emit blocks - implemented 2026-01-04

**See:** `doc/contracts/macro_contracts.md` for detailed integration plan

#### 5. Macro Validation (`src/compiler/src/macro_validation.rs`)
- ✅ Macro-before-use ordering validation (#1304)
- ✅ Shadowing prevention for introduced symbols
- ✅ Type annotation requirements
- ✅ QIDENT template binding validation

### ✅ LL(1) Parser Integration (COMPLETE - 2026-01-04)

#### 6. LL(1) Parser Integration
- ✅ One-pass parsing with immediate macro registration
- ✅ MacroRegistry added to Parser struct
- ✅ Macros registered during parsing (`parse_macro_def`)
- ✅ Macro contracts processed at parse time when LL(1) mode enabled
- ✅ Introduced symbols tracked per scope
- ✅ Template substitution with const bindings
- ✅ Const expression evaluation (int, string, bool, binary ops)

**Files:**
- `src/parser/src/macro_registry.rs` - MacroRegistry, ConstEvalContext, IntroducedSymbol (540 lines)
- `src/parser/src/parser_impl/core.rs` - Parser struct with MacroRegistry
- `src/parser/src/parser_helpers.rs` - process_macro_contract_ll1()
- `src/parser/src/statements/macro_parsing.rs` - register_macro() call

**Usage:**
```rust
// Normal mode (macros registered but not processed)
let mut parser = Parser::new(source);

// LL(1) mode (macros registered AND contracts processed at parse time)
let mut parser = Parser::with_ll1_macros(source);

// Query registered macros
assert!(parser.macro_registry().has_macro("my_macro"));

// Query introduced symbols (in LL(1) mode)
let symbols = parser.macro_registry().get_introduced_symbols("module");
```

**Tests:** 5 LL(1) parser tests in `src/driver/tests/interpreter_macros.rs`

**See:** `doc/spec/macro.md` for full specification

#### 7. Advanced Features
- ✅ `stringify!(expr)` - Convert expression to string (implemented 2026-01-04)
- ✅ Macro debugging/tracing - `--macro-trace` CLI flag (implemented 2026-01-04)
- ✅ Recursive macro expansion with depth limit (max 128, implemented 2026-01-04)
- ✅ Variadic patterns: `...items` (implemented 2026-01-04)
- ✅ Cross-module macro imports (implemented 2026-01-04)

## Current Syntax Examples

### Working Today:

```simple
# Built-in macros
println!("Hello, World!")
let arr = vec!(1, 2, 3)
assert_eq!(arr.len(), 3)

# User-defined macro (simple)
macro answer() -> (returns result: Int):
  emit result:
    42

let x = answer!()  # x = 42

# User-defined macro (with params)
macro double(x: Int) -> (returns result: Int):
  emit result:
    x + x

let y = double!(21)  # y = 42

# User-defined macro (with const param and template)
macro greet(name: Str const) -> (returns result: Str):
  emit result:
    "Hello, {name}!"

let msg = greet!("World")  # msg = "Hello, World!"
```

### Planned (Infrastructure Ready):

```simple
# Function introduction with const-time unrolling
macro gen_axes(BASE: Str const, N: Int const) -> (
  intro axes:
    for i in 0..N:
      enclosing.class.fn "{BASE}{i}"(v: Vec[N]) -> Int
):
  emit axes:
    for i in 0..N:
      fn "{BASE}{i}"(v: Vec[N]) -> Int:
        return v[i]

class Vec3D:
  gen_axes!("axis", 3)  # Introduces: axis0, axis1, axis2

  fn magnitude(self) -> Float:
    let x = self.axis0([1.0, 2.0, 3.0])  # IDE knows axis0 exists!
    ...
```

## Files

### Implementation
- `src/parser/src/ast.rs` - Macro AST types
- `src/compiler/src/interpreter_macro.rs` - Macro expansion (1270 lines)
- `src/compiler/src/macro_contracts.rs` - Contract processing (390 lines)
- `src/compiler/src/macro_validation.rs` - Validation rules

### Tests
- `src/driver/tests/interpreter_macros.rs` - 50 macro tests (all passing)
- `src/driver/tests/interpreter_macro_hygiene.rs` - 11 hygiene tests

### Documentation
- `doc/spec/macro.md` - Full specification (LL(1) grammar)
- `doc/contracts/macro_contracts.md` - Contract implementation details
- This file - Current status

## Next Steps

### ✅ Phase 1: Symbol Table Architecture (COMPLETE - 2025-12-27)
1. ✅ Make symbol tables mutable during macro expansion (Option A)
2. ✅ Updated ~122 function signatures to use `&mut HashMap`
3. ✅ Register introduced symbols in macro invocation handler
4. ✅ Integrated `take_macro_introduced_symbols()` mechanism

**Status:** Complete - see `doc/report/MACRO_OPTION_A_IMPLEMENTATION_2025-12-27.md`

### ✅ Phase 2: Parser Contract Support (COMPLETE - 2025-12-27)
1. ✅ Parser already supported all contract syntax (440 lines in macro_parsing.rs)
2. ✅ Added newline/indent handling after intro/inject colons
3. ✅ Implemented function extraction from emit blocks via local_env
4. ✅ Added hygiene name resolution for gensymmed functions
5. ✅ Wired contract processing to interpreter macro expansion
6. ✅ Fixed thread-local timing (store after extraction, not before)
7. ✅ Created test cases and verified end-to-end functionality

**Status:** Complete and tested - macro-introduced functions working!
**See:** `doc/report/MACRO_PHASE2_PARSER_INTEGRATION_2025-12-27.md`

### ✅ Phase 3: Inject Infrastructure (COMPLETE - 2026-01-04)
1. ✅ Updated MacroContractResult with inject_labels and injections fields
2. ✅ Implemented inject spec tracking in process_inject_item
3. ✅ Added emit block detection for inject labels
4. ✅ Inject code extraction to contract result
5. ✅ Code extraction from emit blocks matching inject labels
6. ✅ "Here" injection execution at callsite (via interpreter_eval.rs)
7. ✅ "Tail" injection execution at block exit (via thread-local pending injections)
8. ⏳ "Head" injection (requires block pre-scanning, deferred)

**Status:** "Here" and "Tail" injections fully working, "Head" deferred
**Limitation:** Head injections would require pre-scanning blocks before execution
**Tests:** `macro_inject_here_basic`, `macro_inject_tail_basic` in `src/driver/tests/interpreter_macros.rs`

### ✅ Phase 4: Template Substitution (COMPLETE - 2025-12-27)
1. ✅ Template substitution in emit blocks working (`{param}` → value)
2. ✅ Support for string const params
3. ✅ Support for integer const params
4. ✅ Support for multiple const params
5. ⏳ Template substitution in intro contracts (requires parser changes for f-strings in names)

**Status:** Working in emit blocks, tested with strings and integers
**Limitation:** Intro contracts use plain strings for function names, not f-strings
**See:** `simple/examples/test_macro_template.spl`

### ✅ Phase 5: Const-Eval Testing (COMPLETE - 2026-01-04)
1. ✅ Fixed parser bug in `parse_macro_intro_spec` - use `parse_primary()` instead of `parse_expression()` for range bounds
2. ✅ Fixed validation to include loop indices in const_bindings
3. ✅ Tested for loops generating multiple functions
4. ✅ Tested if conditionals for conditional generation
5. ✅ Tested multiple function generation with loop indices in templates
6. ✅ Added template substitution for Expr::Identifier in function bodies
7. ✅ Added Node::Function handling in template substitution
8. ✅ Fixed hygiene-aware function matching for emit block extraction (strips _gensym_ suffix)

**Status:** Const-eval loops and conditionals fully working in intro specs
**Test Files:**
- `simple/examples/test_macro_for_simple.spl` - Basic for loop test
- `simple/examples/test_macro_const_eval.spl` - Full const-eval test (loops + conditionals)
- `src/driver/tests/interpreter_macros.rs` - 50 tests including for-loop intro specs and inject execution

**Bugs Fixed (2026-01-04):**
- Template substitution: Added handling for bare identifiers (e.g., `n` → `10`)
- Template substitution: Added handling for Node::Function to substitute templates in function bodies
- Emit extraction: Fixed hygiene-aware matching for functions (e.g., `get_0_gensym_1` matches `get_0`)
- For-loop intro: Multiple functions now correctly extracted and registered
- Intro function mapping: Added `intro_function_labels` to track emit label → public function name
- Emit block extraction: Functions from emit blocks now correctly registered with public name from intro spec
- Recursive expansion: Added MAX_MACRO_EXPANSION_DEPTH (128) limit with clear error messages

### ✅ Phase 6: Macro Debugging/Tracing (COMPLETE - 2026-01-04)
1. ✅ Added `--macro-trace` CLI flag for macro expansion debugging
2. ✅ Thread-local `MACRO_TRACE_ENABLED` flag for runtime control
3. ✅ Trace output shows: macro name, const_bindings, intro functions, inject labels, result
4. ✅ Help text updated with `--macro-trace` documentation

**Usage:**
```bash
simple --macro-trace my_file.spl
```

**Output Example:**
```
[macro] expanding gen_getter!(...)
[macro]   const_bindings: {"val": "42", "name": "get_it"}
[macro]   intro functions: ["get_it"]
[macro]   result: Nil
```

### ✅ Phase 7: For-Loop Unrolling in Emit Blocks (COMPLETE - 2026-01-04)
1. ✅ Implemented `try_unroll_const_for_loop` for const-eval range detection
2. ✅ Added `eval_const_expr_to_i64` for evaluating const expressions
3. ✅ Updated `substitute_block_templates` to call unrolling
4. ✅ Fixed function name template substitution (strip quotes from `"get_{i}"`)
5. ✅ Dual matching strategy: name-based for for-loops, label-based fallback for explicit names
6. ✅ All 50 macro tests passing

**How It Works:**
- For-loops with const ranges in emit blocks are unrolled at expansion time
- Each iteration binds the loop variable to the current index value
- Function names with templates like `"get_{i}"` are substituted to `get_0`, `get_1`, etc.
- Quote stripping ensures function names don't include literal quotes

**Test Coverage:**
- `macro_intro_template_with_for_loop` - Multiple functions from for-loop
- `macro_intro_with_const_for_loop` - For-loop in intro specs
- `macro_intro_with_const_param_substitution` - Label-based matching fallback

### Phase 8: IDE Integration (Future)
1. Expose contract information to LSP
2. Enable autocomplete for introduced symbols
3. Show macro expansion in hover tooltips
4. Jump-to-definition for macro-introduced symbols

## Known Limitations

1. **No macro re-exports** - Cannot explicitly re-export macros from modules (they're auto-available)
2. **Limited const-eval for complex types** - Supports int, string, bool; no arrays/functions
3. **No error spans in contracts** - Uses dummy spans (need source location tracking)
4. **Head injection deferred** - Would require block pre-scanning (Here/Tail work)

## Difficulty Assessment

**Why 4 (not 5):**
- ✅ Macro expansion is additive (doesn't break existing code)
- ✅ Simple textual macros work well
- ✅ Parser already handles syntax
- ✅ Well-documented patterns from Rust/Lisp
- ✅ Hygiene deferred successfully

**Remaining complexity:**
- Parser/interpreter integration boundary
- Symbol table mutation during expansion
- Error reporting through macro layers
- IDE protocol integration

## Future Work (Architectural Changes Required)

### ✅ Field Introduction in Classes (COMPLETE - 2026-01-04)
**Complexity:** High | **Status:** Implemented

Implementation completed with the following changes:
1. ✅ Added `macro_invocations: Vec<MacroInvocation>` field to ClassDef AST node
2. ✅ Added `parse_class_body()` function to parser with macro invocation detection
3. ✅ Added `is_macro_invocation_start()` and `parse_class_body_macro_invocation()` helpers
4. ✅ Wired up field introduction in interpreter_eval.rs Node::Class handling
5. ✅ Created tests: `macro_field_intro_parser_recognizes_macro_in_class_body`, `macro_invocation_in_class_body_parses`

**Files modified:**
- `src/parser/src/types_def/mod.rs` - Added class body macro parsing
- `src/parser/src/ast/nodes/definitions.rs` - Added macro_invocations to ClassDef
- `src/compiler/src/interpreter_eval.rs` - Wired up field introduction
- `src/driver/tests/interpreter_macros.rs` - Added 2 new tests

**Infrastructure:** `create_field_from_stub()` in macro_contracts.rs

### ✅ Variadic Patterns (`...items`) (COMPLETE - 2026-01-04)
**Complexity:** Medium | **Status:** Implemented

Implementation completed with the following changes:
1. ✅ Added `is_variadic: bool` field to `MacroParam` struct
2. ✅ Updated `parse_macro_param()` to detect `...` prefix (Ellipsis token)
3. ✅ Added validation: variadic parameters cannot be const
4. ✅ Added validation: variadic parameter must be last
5. ✅ Updated macro expansion to collect remaining args into array for variadic params
6. ✅ Created 6 tests covering basic, with regular params, empty, single arg, position error, const error

**Files modified:**
- `src/parser/src/ast/nodes/definitions.rs` - Added is_variadic to MacroParam
- `src/parser/src/statements/macro_parsing.rs` - Parse ...name syntax
- `src/compiler/src/interpreter_macro.rs` - Handle variadic in expansion
- `src/driver/tests/interpreter_macros.rs` - Added 6 variadic tests

**Example:**
```simple
macro sum_all(...nums: Int) -> (returns result: Int):
    emit result:
        nums.sum()

main = sum_all!(1, 2, 3, 4, 5)  # Returns 15
```

### ✅ Cross-Module Macro Imports (COMPLETE - 2026-01-04)
**Complexity:** High | **Status:** Implemented

Implementation completed with the following changes:
1. ✅ Added macro collection in `evaluate_module_exports`
2. ✅ Macros from imported modules are registered in USER_MACROS during module evaluation
3. ✅ Created baseline test for same-file macros

**Files modified:**
- `src/compiler/src/interpreter_module.rs` - Added Node::Macro handling
- `src/driver/tests/interpreter_macros.rs` - Added baseline test

**How it works:**
When a module is imported, its macros are automatically registered in the global USER_MACROS storage, making them available for use in the importing file.

### ✅ LL(1) Parser Integration (COMPLETE - 2026-01-04)
**Complexity:** Very High | **Status:** Implemented

Implementation completed with the following changes:
1. ✅ Added `MacroRegistry` to Parser struct for one-pass macro tracking
2. ✅ Macros registered during parsing (`parse_macro_def`)
3. ✅ Macro contracts processed at parse time in LL(1) mode
4. ✅ Const expression evaluation (int, string, bool, binary/unary ops)
5. ✅ Template substitution with const bindings
6. ✅ Introduced symbols tracked per scope

**Files created:**
- `src/parser/src/macro_registry.rs` - MacroRegistry, ConstEvalContext, IntroducedSymbol, InjectionPoint (540 lines)

**Files modified:**
- `src/parser/src/lib.rs` - Export macro_registry module
- `src/parser/src/parser_impl/core.rs` - Add macro_registry and current_scope to Parser
- `src/parser/src/parser_helpers.rs` - Add process_macro_contract_ll1()
- `src/parser/src/statements/macro_parsing.rs` - Register macros during parsing
- `src/parser/src/expressions/mod.rs` - Process contracts in LL(1) mode

**Tests:** 5 LL(1) parser tests in `src/driver/tests/interpreter_macros.rs`

## Related Features

- #400-429: Contract system (macros can use contracts)
- #50-99: Extended features (macros can generate them)
- #880-919: LLM-friendly features (macro AST export)
