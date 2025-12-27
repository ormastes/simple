# Feature #34: Macros - Implementation Status

**Status**: Partially Implemented (75% complete)
**Difficulty**: 4 (was 5)
**Importance**: 3
**Last Updated**: 2025-12-27

## Summary

Compile-time macros for code generation and metaprogramming. Basic macro expansion is working with built-in and user-defined macros. Symbol table architecture updated to support dynamic registration (Option A complete). Contract parsing integration pending.

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

**Test Coverage:** 9 tests in `src/driver/tests/interpreter_macros.rs`

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
- ✅ Symbol table integration - mutable architecture implemented (Option A complete)
- ✅ Symbol registration - macros can now register functions/classes
- ✅ Thread-local handoff - MACRO_INTRODUCED_SYMBOLS working

**What's Missing:**
- ⏳ Contract parsing - parser doesn't support intro/inject syntax yet (#1304)
- ⏳ IDE autocomplete support - infrastructure ready but not exposed
- ⏳ Inject execution - injection points tracked but code not spliced
- ⏳ Field introduction - requires class context analysis

**See:** `doc/contracts/macro_contracts.md` for detailed integration plan

#### 5. Macro Validation (`src/compiler/src/macro_validation.rs`)
- ✅ Macro-before-use ordering validation (#1304)
- ✅ Shadowing prevention for introduced symbols
- ✅ Type annotation requirements
- ✅ QIDENT template binding validation

### ❌ Not Yet Implemented

#### 6. LL(1) Parser Integration
- ❌ One-pass parsing with immediate symbol registration
- ❌ Parser-driven macro expansion (currently interpreter-driven)
- ❌ FIRST/FOLLOW set implementation from spec

**See:** `doc/spec/macro.md` for full specification

#### 7. Advanced Features
- ❌ `stringify!(expr)` - Convert expression to string
- ❌ Variadic patterns: `...items`
- ❌ Recursive macro expansion
- ❌ Macro debugging/tracing
- ❌ Cross-module macro imports

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
- `src/driver/tests/interpreter_macros.rs` - 13 macro tests
- `src/driver/tests/interpreter_macro_hygiene.rs` - Hygiene tests

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

### Phase 2: Parser Contract Support (Estimated: 3-5 hours) - NEXT
1. Parse `intro` items with targets (enclosing.module, enclosing.class, etc.)
2. Parse `inject` items with positions (Head, Tail, Here)
3. Parse `returns` items with labels
4. Wire parsed contracts to existing infrastructure
5. Add integration tests for contract syntax

### Phase 3: Inject Support (Estimated: 2-3 hours)
1. Implement code injection at callsite
2. Handle Head/Tail/Here anchor points
3. Splice injected code into surrounding block
4. Test injection behavior

### Phase 4: IDE Integration (Future)
1. Expose contract information to LSP
2. Enable autocomplete for introduced symbols
3. Show macro expansion in hover tooltips
4. Jump-to-definition for macro-introduced symbols

## Known Limitations

1. **No cross-module macros** - Macros must be defined in same file as use
2. **No macro re-exports** - Cannot export macros from modules
3. **Limited const-eval** - Only integers, no strings/arrays/functions
4. **No error spans in contracts** - Uses dummy spans (need source location tracking)
5. **No recursion limits** - Could cause stack overflow on deeply nested const-eval
6. **Field introduction incomplete** - Requires class context analysis

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

## Related Features

- #400-429: Contract system (macros can use contracts)
- #50-99: Extended features (macros can generate them)
- #880-919: LLM-friendly features (macro AST export)
