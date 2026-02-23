# Macro Type Checking Implementation Plan

**Date:** 2026-02-03
**Phase:** 7 of Rust Feature Parity Roadmap
**Total Time:** 15 hours
**Status:** Planning

---

## Overview

Implement type checking for macros to validate macro definitions, arguments, and expansions. Ensures macro usage is type-safe and expansions produce well-typed code.

**Key Concept:**
```simple
# Macro definition with type checking
@macro my_assert(cond: bool, msg: text):
    if not cond:
        panic(msg)

# Valid usage
@my_assert(x > 0, "x must be positive")

# Invalid usage (type error)
@my_assert("hello", 42)  # ERROR: wrong argument types
```

---

## Background: Macro Type Checking

### Definition

**Macro Type Checking** validates:
1. **Macro definitions** - parameter types, body well-typedness
2. **Macro calls** - argument types match parameters
3. **Macro expansions** - expanded code is well-typed

### Why Macro Type Checking Matters

**Safety:**
```simple
# Without type checking:
@macro bad_swap(a, b):
    val temp = a
    a = b        # ERROR: might not be assignable
    b = temp

bad_swap(x, "hello")  # Runtime error!

# With type checking:
@macro swap<T>(a: T, b: T):
    val temp = a
    a = b        # OK: both T
    b = temp

swap(x, "hello")  # ERROR: type mismatch (i32 vs String)
```

**Hygiene:**
```simple
# Macro should not capture variables from call site
@macro increment(x):
    val temp = x + 1  # 'temp' should not conflict with caller's 'temp'
    x = temp
```

---

## Current Status

### Simple's Macros

Simple has basic macro support but no type checking:

```simple
# Macros are expanded without type validation
@my_macro(x, y)  # No check that arguments are correct types
```

### Missing Features

1. ✅ **Already have:** Macro expansion (AST → AST)
2. ❌ **Need:** Macro definition tracking
3. ❌ **Need:** Parameter type annotations
4. ❌ **Need:** Argument type checking
5. ❌ **Need:** Expansion type inference
6. ❌ **Need:** Hygiene checking

---

## Phase Breakdown

### Phase 7A: Macro Definition Representation (3 hours)

**Goal:** Define macro representation with type information

**Data Structures:**

```simple
# Macro parameter with type
class MacroParam:
    name: Symbol
    ty: HirType
    is_variadic: bool  # For ...args

# Macro definition
class MacroDef:
    name: Symbol
    params: [MacroParam]
    body: Expr           # Macro body (AST)
    expansion_ty: HirType  # Result type of expansion
    hygiene_scope: i64   # Scope ID for hygiene

# Macro registry
class MacroRegistry:
    macros: text  # Dict<Symbol, MacroDef>

    me register_macro(macro_def: MacroDef)
    fn lookup_macro(name: Symbol) -> MacroDef?
    fn has_macro(name: Symbol) -> bool
```

**Examples:**

```simple
# Example 1: Simple macro
@macro assert(cond: bool, msg: text):
    if not cond:
        panic(msg)

# MacroDef:
# - name: "assert"
# - params: [
#     MacroParam(name: "cond", ty: Bool, is_variadic: false),
#     MacroParam(name: "msg", ty: String, is_variadic: false)
#   ]
# - body: If(Not(Var("cond")), Call(Var("panic"), [Var("msg")]))
# - expansion_ty: Unit

# Example 2: Variadic macro
@macro log(level: text, ...args: [text]):
    for arg in args:
        println("[{level}] {arg}")

# MacroDef:
# - params: [
#     MacroParam(name: "level", ty: String, is_variadic: false),
#     MacroParam(name: "args", ty: [String], is_variadic: true)
#   ]
```

**Tests:**
- MacroParam creation
- MacroDef creation
- MacroRegistry registration/lookup
- Variadic parameter handling

---

### Phase 7B: Macro Call Type Checking (4 hours)

**Goal:** Validate macro call arguments against parameter types

**Algorithm:**

```simple
class MacroTypeChecker:
    registry: MacroRegistry
    type_env: TypeEnv

    fn check_macro_call(call: MacroCall) -> Result<HirType, TypeError>:
        """
        Type check a macro call

        Steps:
        1. Lookup macro definition
        2. Check argument count matches parameters
        3. Infer argument types
        4. Check each argument matches parameter type
        5. Return expansion type
        """
        # 1. Lookup
        val macro_def = self.registry.lookup_macro(call.name)?

        # 2. Check arity
        if not self.check_arity(call.args, macro_def.params):
            return Error("Macro {call.name}: wrong number of arguments")

        # 3-4. Check argument types
        for i, (arg, param) in call.args.zip(macro_def.params).enumerate():
            val arg_ty = self.infer_expr(arg)?

            if not self.check_subtype(arg_ty, param.ty):
                return Error("Macro {call.name}: argument {i} has type {arg_ty}, expected {param.ty}")

        # 5. Return expansion type
        Ok(macro_def.expansion_ty)

    fn check_arity(args: [Expr], params: [MacroParam]) -> bool:
        """Check argument count matches parameters (handle variadic)"""
        val non_variadic_count = params.filter(\p: not p.is_variadic).len()
        val has_variadic = params.any(\p: p.is_variadic)

        if has_variadic:
            # At least non_variadic_count arguments
            args.len() >= non_variadic_count
        else:
            # Exact match
            args.len() == non_variadic_count
```

**Examples:**

```simple
# Example 1: Valid call
@macro add(x: i32, y: i32) -> i32:
    x + y

val result = @add(1, 2)  # OK: both i32

# Example 2: Invalid call (type mismatch)
val result = @add(1, "hello")  # ERROR: second arg is String, not i32

# Example 3: Invalid call (wrong arity)
val result = @add(1)  # ERROR: expected 2 arguments, got 1

# Example 4: Variadic call
@macro join(...strs: [text]) -> text:
    strs.join(", ")

val result = @join("a", "b", "c")  # OK: 3 arguments
val result2 = @join()              # OK: 0 arguments (empty list)
```

**Tests:**
- Valid macro call
- Invalid call (type mismatch)
- Invalid call (wrong arity)
- Variadic macro calls
- Nested macro calls

---

### Phase 7C: Macro Expansion Type Inference (5 hours)

**Goal:** Infer result type of macro expansion

**Algorithm:**

```simple
class MacroExpander:
    type_checker: MacroTypeChecker

    me expand_and_check(call: MacroCall) -> Result<(Expr, HirType), TypeError>:
        """
        Expand macro and infer result type

        Steps:
        1. Check macro call is valid
        2. Substitute arguments into body
        3. Type check expanded body
        4. Return expanded expression and type
        """
        # 1. Check call
        val expected_ty = self.type_checker.check_macro_call(call)?

        # 2. Expand
        val macro_def = self.type_checker.registry.lookup_macro(call.name)?
        val expanded = self.substitute_params(macro_def.body, macro_def.params, call.args)

        # 3. Type check expansion
        val actual_ty = self.type_checker.infer_expr(expanded)?

        # 4. Verify expansion type matches definition
        if not self.type_checker.check_subtype(actual_ty, expected_ty):
            return Error("Macro expansion has type {actual_ty}, expected {expected_ty}")

        Ok((expanded, actual_ty))

    fn substitute_params(body: Expr, params: [MacroParam], args: [Expr]) -> Expr:
        """
        Substitute macro parameters with arguments in body

        Handles:
        - Simple substitution (param → arg)
        - Variadic expansion (...args → [arg1, arg2, ...])
        - Hygiene (rename bound variables to avoid capture)
        """
        var subst_map = {}

        for i, (param, arg) in params.zip(args).enumerate():
            if param.is_variadic:
                # Collect remaining args into list
                val remaining = args[i..]
                subst_map[param.name] = Expr.List(remaining)
            else:
                subst_map[param.name] = arg

        self.apply_substitution(body, subst_map)
```

**Examples:**

```simple
# Example 1: Simple expansion
@macro double(x: i32) -> i32:
    x + x

val result = @double(5)

# Expansion:
# 1. Substitute: x → 5
# 2. Body becomes: 5 + 5
# 3. Type check: i32 + i32 → i32
# 4. Result: (Expr(5 + 5), i32)

# Example 2: Control flow expansion
@macro unless(cond: bool, body: Expr):
    if not cond:
        body

@unless(x < 0):
    print("x is non-negative")

# Expansion:
# 1. Substitute: cond → (x < 0), body → print(...)
# 2. Body becomes: if not (x < 0): print(...)
# 3. Type check: if bool: Unit → Unit
# 4. Result: (If(...), Unit)

# Example 3: Variadic expansion
@macro sum(...nums: [i32]) -> i32:
    var total = 0
    for num in nums:
        total = total + num
    total

val result = @sum(1, 2, 3, 4)

# Expansion:
# 1. Substitute: nums → [1, 2, 3, 4]
# 2. Body becomes: var total = 0; for num in [1,2,3,4]: ...; total
# 3. Type check: i32
# 4. Result: (expanded_expr, i32)
```

**Tests:**
- Simple expansion
- Control flow expansion
- Variadic expansion
- Nested expansion
- Hygiene (variable capture avoidance)

---

### Phase 7D: Hygiene & Integration (3 hours)

**Goal:** Ensure macro hygiene and integrate with type checker

**Hygiene:**

```simple
class HygieneChecker:
    """
    Ensures macro expansions don't capture variables from call site

    Approach: Alpha-renaming
    - Rename all bindings introduced in macro body
    - Use unique names (e.g., temp$macro$123)
    """
    fresh_id: i64

    me rename_bindings(body: Expr, hygiene_scope: i64) -> Expr:
        """
        Rename all variable bindings in macro body

        Avoids capture:
        - Macro introduces 'temp' → renamed to 'temp$macro$123'
        - Call site has 'temp' → unaffected
        """
        match body:
            case Let(name, value, rest):
                val new_name = "{name}$macro${hygiene_scope}${self.fresh_id}"
                self.fresh_id = self.fresh_id + 1

                # Rename binding and all references in rest
                val renamed_rest = self.rename_var(rest, name, new_name)
                Expr.Let(new_name, value, renamed_rest)

            case _:
                # Recursively rename in subexpressions
                self.rename_in_subexprs(body, hygiene_scope)

    fn rename_var(expr: Expr, old_name: Symbol, new_name: Symbol) -> Expr:
        """Rename all occurrences of old_name to new_name"""
        match expr:
            case Var(name):
                if name == old_name:
                    Expr.Var(new_name)
                else:
                    expr

            case _:
                # Recursively rename in subexpressions
                self.rename_in_subexprs_simple(expr, old_name, new_name)
```

**Examples:**

```simple
# Example: Variable capture avoidance
@macro with_temp(x: i32) -> i32:
    val temp = x * 2
    temp + 1

fn caller():
    val temp = 5
    val result = @with_temp(10)  # Should not affect caller's 'temp'
    print(temp)  # Should print 5, not modified

# Without hygiene:
# Expansion: val temp = 10 * 2; temp + 1
# Problem: Overwrites caller's 'temp'!

# With hygiene:
# Expansion: val temp$macro$123 = 10 * 2; temp$macro$123 + 1
# Result: Caller's 'temp' unaffected
```

**Integration:**

```simple
# In type checker:
me infer_expr(expr: Expr) -> Result<HirType, TypeError>:
    match expr:
        case MacroCall(name, args):
            # 1. Expand macro
            val (expanded, ty) = self.macro_expander.expand_and_check(MacroCall(name, args))?

            # 2. Apply hygiene
            val hygienic = self.hygiene_checker.rename_bindings(expanded, self.current_scope)

            # 3. Type check expanded expression
            self.infer_expr(hygienic)?

        case _:
            # Other expression types
            ...
```

**Tests:**
- Variable capture avoidance
- Nested binding renaming
- Integration with type checker
- Error messages for macro errors

---

## Examples

### Example 1: Type-Safe Assert Macro

```simple
@macro assert(cond: bool, msg: text):
    if not cond:
        panic(msg)

# Valid usage
fn validate(x: i32):
    @assert(x > 0, "x must be positive")
    @assert(x < 100, "x must be less than 100")

# Invalid usage
@assert(42, "this is wrong")  # ERROR: first arg must be bool
@assert(true)                 # ERROR: missing second argument
```

### Example 2: Generic Macro

```simple
@macro swap<T>(a: T, b: T):
    val temp = a
    a = b
    b = temp

# Valid usage
var x = 1
var y = 2
@swap(x, y)  # OK: both i32

var s1 = "hello"
var s2 = "world"
@swap(s1, s2)  # OK: both String

# Invalid usage
@swap(x, s1)  # ERROR: type mismatch (i32 vs String)
```

### Example 3: Variadic Logging Macro

```simple
@macro log(level: text, ...msgs: [text]):
    for msg in msgs:
        println("[{level}] {msg}")

# Valid usage
@log("INFO", "Starting application")
@log("DEBUG", "Value 1", "Value 2", "Value 3")
@log("ERROR")  # OK: no messages

# Invalid usage
@log(42, "message")  # ERROR: first arg must be text
@log("INFO", 123)    # ERROR: variadic args must be text
```

### Example 4: Control Flow Macro

```simple
@macro unless(cond: bool, body: Expr):
    if not cond:
        body

# Valid usage
@unless(x < 0):
    print("x is non-negative")

# Invalid usage
@unless("hello"):  # ERROR: condition must be bool
    print("...")
```

### Example 5: Hygiene Example

```simple
@macro with_logging(action: Expr) -> text:
    val result = action  # 'result' should not capture caller's 'result'
    print("Action completed")
    result

fn caller():
    val result = "original"
    val new_result = @with_logging("new value")
    print(result)  # Should print "original", not affected by macro
```

---

## Testing Strategy

### Test Categories

1. **Macro Definition (Phase 7A):**
   - MacroParam creation
   - MacroDef with various parameter types
   - MacroRegistry operations
   - Variadic parameters

2. **Macro Call Checking (Phase 7B):**
   - Valid macro calls
   - Type mismatch errors
   - Arity errors
   - Variadic calls

3. **Expansion Type Inference (Phase 7C):**
   - Simple expansions
   - Control flow expansions
   - Variadic expansions
   - Nested macro calls

4. **Hygiene (Phase 7D):**
   - Variable capture avoidance
   - Nested bindings
   - Integration with type checker

### Test Count: ~25 tests

---

## Performance Characteristics

### Time Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Macro lookup | O(1) | Hash map lookup |
| Argument type checking | O(n × m) | n = args, m = type checking cost |
| Expansion | O(s) | s = size of macro body |
| Hygiene renaming | O(s × b) | s = body size, b = bindings |

### Space Complexity

| Structure | Complexity | Notes |
|-----------|-----------|-------|
| MacroRegistry | O(m × p) | m = macro count, p = params per macro |
| Expanded expressions | O(s × c) | s = body size, c = call count |

---

## Integration with Existing Systems

### 1. Type Checker Integration

```simple
# In type_infer.spl
me infer_expr(expr: Expr) -> Result<HirType, TypeError>:
    match expr:
        case MacroCall(name, args):
            # Expand and check macro
            val (expanded, ty) = self.macro_expander.expand_and_check(MacroCall(name, args))?
            return Ok(ty)

        case _:
            # Other expressions
            ...
```

### 2. Trait System (Phase 2)

Macros can use trait bounds:

```simple
@macro sort_items<T: Ord>(items: [T]) -> [T]:
    items.sort()
```

### 3. Generic Types (Phase 4)

Macros can be generic:

```simple
@macro unwrap<T>(opt: Option<T>) -> T:
    match opt:
        case Some(x): x
        case None: panic("unwrap on None")
```

### 4. Higher-Rank Types (Phase 5)

Macros can use higher-rank types:

```simple
@macro with_ref<T>(value: T, f: forall U. fn(T) -> U) -> U:
    f(value)
```

---

## Limitations

### 1. No Procedural Macros

Current implementation supports declarative macros only:

```simple
# Supported: Declarative (pattern-based)
@macro my_macro(x: T):
    body

# Not supported: Procedural (code generation)
#[proc_macro]
fn my_proc_macro(input: TokenStream) -> TokenStream {
    // Rust-style procedural macro
}
```

**Future:** Add procedural macro support with token stream manipulation.

### 2. No Macro Recursion

Recursive macro expansion not implemented:

```simple
# Not supported: Recursive macro
@macro repeat(n: i32, body: Expr):
    if n > 0:
        body
        @repeat(n - 1, body)  # ERROR: recursive expansion
```

**Future:** Add recursion depth tracking and limits.

### 3. Limited Hygiene

Current hygiene is basic (alpha-renaming):

```simple
# Basic hygiene works:
@macro with_temp(x: i32):
    val temp = x
    temp

# But doesn't handle:
# - Macro-defined macros
# - Cross-module hygiene
# - Syntax classes
```

**Future:** Implement full hygiene with syntax marks/scopes.

---

## Next Steps

After Phase 7:
1. **Phase 8:** Const Keys (6h)
2. **Phase 9:** SIMD Complete (4h)
3. **Phase 1:** Bidirectional Type Checking (12h) - deferred

---

## File Structure

```
src/compiler/
  macro_checker_phase7a.spl      # Macro definitions (3h)
  macro_checker_phase7b.spl      # Call type checking (4h)
  macro_checker_phase7c.spl      # Expansion inference (5h)
  macro_checker_phase7d.spl      # Hygiene & integration (3h)

doc/plan/
  macro_type_checking_implementation_plan.md  # This file

doc/report/
  macro_type_checking_complete_2026-02-03.md  # To be created
```

---

## Success Criteria

✅ All 4 phases implemented
✅ 25+ tests passing
✅ Macro definitions tracked with types
✅ Macro calls type checked
✅ Expansions type inferred
✅ Basic hygiene implemented
✅ Integration with type checker
✅ Error messages for macro errors

---

**Status:** Ready to implement
**Next:** Phase 7A - Macro Definition Representation (3 hours)
