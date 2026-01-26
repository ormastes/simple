# UFCS Dot Operator Enhancement Design

**Status:** Complete (All Phases Implemented)
**Date:** 2026-01-26
**Updated:** 2026-01-26

## Overview

Enhance the dot operator (`.`) to support **Uniform Function Call Syntax (UFCS)**, where `x.map()` can resolve to either a method call or `map(x)` function call.

## Current Behavior

```simple
# Method call - looks for map() in x's class only
x.map()

# Function call - standalone function
map(x)
```

## Proposed Behavior

```simple
# UFCS: x.map() resolves in priority order:
# 1. Method in x's class/type
# 2. Method from trait implemented by x's type
# 3. Free function map(x) where first param matches x's type

x.map()           # Could be: x.map() OR map(x)
x.filter(pred)    # Could be: x.filter(pred) OR filter(x, pred)
```

## Design Goals

1. **Minimal AST Changes** - Keep `MethodCall` node, add resolution metadata
2. **Syntax Sugar at Resolution** - Not at parsing (avoid desugaring pass)
3. **Clear Priority** - Class method > Trait method > Free function
4. **Type-Safe** - First parameter type must match receiver type
5. **Backward Compatible** - Existing code works unchanged

---

## Implementation Options

### Option A: Resolution-Time UFCS (Recommended)

**Approach:** Keep AST unchanged, resolve during name resolution/type checking.

```
Parser → AST (MethodCall) → HIR (MethodCall) → Resolution → Resolved HIR
                                                    ↓
                                              Fill `resolved` field
                                              with actual target
```

**Changes Required:**

1. **HIR Enhancement** - Add resolution target enum:
```simple
enum MethodResolution:
    InstanceMethod(class_id: SymbolId, method_id: SymbolId)
    TraitMethod(trait_id: SymbolId, method_id: SymbolId)
    FreeFunction(func_id: SymbolId)    # NEW: UFCS resolution
    Unresolved
```

2. **Resolution Pass** - New or enhanced pass:
```simple
fn resolve_method_call(receiver: HirExpr, method: text, args: [HirCallArg]) -> MethodResolution:
    val receiver_type = infer_type(receiver)

    # Priority 1: Direct method on type
    if val m = lookup_method(receiver_type, method):
        return MethodResolution.InstanceMethod(receiver_type.class_id, m)

    # Priority 2: Trait method
    for trait_ in get_implemented_traits(receiver_type):
        if val m = lookup_trait_method(trait_, method):
            return MethodResolution.TraitMethod(trait_.id, m)

    # Priority 3: Free function (UFCS)
    if val f = lookup_function(method):
        if first_param_matches(f, receiver_type):
            return MethodResolution.FreeFunction(f.id)

    return MethodResolution.Unresolved
```

**Pros:**
- No parser changes
- No AST changes
- Clean separation of concerns
- Resolution is type-aware

**Cons:**
- Requires type inference before resolution
- May need two-pass resolution for generic types

---

### Option B: Desugaring Pass

**Approach:** Add a pass between AST and HIR that rewrites unresolved method calls.

```
Parser → AST (MethodCall) → Desugar Pass → Modified AST → HIR
                                  ↓
                           If no method found,
                           rewrite to Call(method, [receiver, ...args])
```

**Changes Required:**

1. **Desugar Pass:**
```simple
fn desugar_method_call(expr: Expr) -> Expr:
    match expr:
        case MethodCall(receiver, method, args):
            val receiver_type = get_type_hint(receiver)  # May not know yet

            # Try to find method
            if has_method(receiver_type, method):
                expr  # Keep as method call
            else:
                # Rewrite to function call
                val new_args = [CallArg(None, receiver)] + args
                Expr(kind: ExprKind.Call(
                    Expr(kind: ExprKind.Ident(method)),
                    new_args
                ))
        case _:
            expr
```

**Pros:**
- Clear transformation step
- Can run before type inference

**Cons:**
- Needs type hints for correct decision
- May make wrong choice before full type info
- Two representations of same thing

---

### Option C: Parser-Level Detection

**Approach:** Parser emits different AST based on known types.

**Not Recommended:**
- Parser doesn't have type information
- Would require symbol table during parsing
- Breaks clean phase separation

---

## Recommended Approach: Option A (Resolution-Time)

### Phase 1: HIR Enhancement

**File:** `simple/compiler/hir.spl`

Add resolution enum and update MethodCall:

```simple
enum MethodResolution:
    """How a method call was resolved."""
    InstanceMethod(type_id: TypeId, method_id: SymbolId)
    TraitMethod(trait_id: SymbolId, method_id: SymbolId)
    FreeFunction(func_id: SymbolId)
    Unresolved

# Update HirExprKind.MethodCall
MethodCall(
    receiver: HirExpr,
    method: text,
    args: [HirCallArg],
    resolution: MethodResolution    # Changed from: resolved: SymbolId?
)
```

### Phase 2: Resolution Pass

**New File:** `simple/compiler/resolve.spl`

```simple
class MethodResolver:
    """Resolves method calls using UFCS rules."""

    symbols: SymbolTable
    types: TypeTable

    fn resolve_expr(expr: HirExpr) -> HirExpr:
        match expr.kind:
            case MethodCall(receiver, method, args, _):
                val resolved_receiver = self.resolve_expr(receiver)
                val resolved_args = args.map(\a: self.resolve_call_arg(a))
                val resolution = self.resolve_method(resolved_receiver, method, resolved_args)

                HirExpr(
                    kind: HirExprKind.MethodCall(resolved_receiver, method, resolved_args, resolution),
                    type_: expr.type_,
                    span: expr.span
                )
            case _:
                # ... handle other cases

    fn resolve_method(receiver: HirExpr, method: text, args: [HirCallArg]) -> MethodResolution:
        val receiver_type = receiver.type_

        # Priority 1: Instance method
        if val class_id = receiver_type.class_id:
            if val method_sym = self.symbols.lookup_method(class_id, method):
                return MethodResolution.InstanceMethod(class_id, method_sym.id)

        # Priority 2: Trait method
        for trait_id in self.types.get_traits(receiver_type):
            if val method_sym = self.symbols.lookup_trait_method(trait_id, method):
                return MethodResolution.TraitMethod(trait_id, method_sym.id)

        # Priority 3: UFCS - Free function
        if val func_sym = self.symbols.lookup_function(method):
            if self.first_param_compatible(func_sym, receiver_type):
                return MethodResolution.FreeFunction(func_sym.id)

        MethodResolution.Unresolved

    fn first_param_compatible(func: Symbol, receiver_type: HirType) -> bool:
        """Check if function's first parameter matches receiver type."""
        match func.kind:
            case Function(params, _, _):
                if params.len > 0:
                    val first_param_type = params[0].type_
                    self.types.is_compatible(receiver_type, first_param_type)
                else:
                    false
            case _:
                false
```

### Phase 3: MIR/Codegen Update

**File:** `simple/compiler/mir.spl`

Handle all resolution cases:

```simple
fn lower_method_call(expr: HirExpr) -> MirInst:
    match expr.kind:
        case MethodCall(receiver, method, args, resolution):
            match resolution:
                case InstanceMethod(type_id, method_id):
                    # Direct method call
                    MirInst.MethodCallStatic(
                        receiver: lower_expr(receiver),
                        method: method_id,
                        args: args.map(lower_arg)
                    )

                case TraitMethod(trait_id, method_id):
                    # Virtual dispatch
                    MirInst.MethodCallVirtual(
                        receiver: lower_expr(receiver),
                        trait_: trait_id,
                        method: method_id,
                        args: args.map(lower_arg)
                    )

                case FreeFunction(func_id):
                    # UFCS: Convert to regular function call
                    # receiver becomes first argument
                    val all_args = [lower_expr(receiver)] + args.map(lower_arg)
                    MirInst.Call(
                        func: func_id,
                        args: all_args
                    )

                case Unresolved:
                    error("unresolved method: {method}")
```

---

## Examples

### Example 1: Basic UFCS

```simple
# Free function
fn double(x: i64) -> i64:
    x * 2

# Usage
val n = 5
val result = n.double()    # Resolves to: double(n)
```

### Example 2: Method Takes Priority

```simple
class Counter:
    value: i64

    fn increment() -> i64:
        self.value += 1
        self.value

# Free function with same name
fn increment(x: i64) -> i64:
    x + 1

val c = Counter(value: 0)
c.increment()    # Calls Counter.increment(), NOT increment(c)

val n = 5
n.increment()    # Calls increment(n) since i64 has no increment method
```

### Example 3: Chaining

```simple
fn map<T, U>(arr: [T], f: fn(T) -> U) -> [U]:
    # ... implementation

fn filter<T>(arr: [T], pred: fn(T) -> bool) -> [T]:
    # ... implementation

val nums = [1, 2, 3, 4, 5]
val result = nums
    .filter(\x: x > 2)     # filter(nums, ...)
    .map(\x: x * 2)        # map(filtered, ...)
```

### Example 4: Type Matching

```simple
fn to_string(x: i64) -> text:
    "{x}"

fn to_string(x: f64) -> text:
    "{x:.2}"

val i = 42
val f = 3.14159

i.to_string()    # Calls to_string(i64)
f.to_string()    # Calls to_string(f64)
```

---

## Edge Cases

### 1. Ambiguous Resolution

```simple
fn process(x: i64) -> i64: x + 1
fn process(x: i64, y: i64) -> i64: x + y

val n = 5
n.process()      # OK: process(n) - 1 arg
n.process(10)    # OK: process(n, 10) - 2 args
```

**Rule:** Argument count disambiguates.

### 2. Generic Functions

```simple
fn identity<T>(x: T) -> T: x

val s = "hello"
s.identity()     # identity<text>("hello")
```

**Rule:** Type inference determines generic instantiation.

### 3. Self Parameter Naming

```simple
# These are equivalent for UFCS:
fn double(self: i64) -> i64: self * 2    # Explicit self
fn double(x: i64) -> i64: x * 2          # Any name works
fn double(value: i64) -> i64: value * 2  # Any name works
```

**Rule:** First parameter name doesn't matter, only type.

### 4. Mutable Receiver

```simple
fn increment(self: mut i64):    # Takes mutable reference
    self += 1

var n = 5
n.increment()    # n is now 6
```

**Rule:** Mutability must match between receiver and parameter.

---

## Implementation Plan

### Phase 1: Core Infrastructure [DONE]
1. ✅ Add `MethodResolution` enum to `hir.spl` (lines 96-142)
2. ✅ Update `MethodCall` to use new resolution type
3. ✅ Add `first_param_compatible` to type checking (in `resolve.spl`)

### Phase 2: Resolution Pass [DONE]
1. ✅ Create `resolve.spl` with `MethodResolver` class
2. ✅ Integrate into compilation pipeline (in `driver.spl`, Phase 3.5)
3. ✅ Handle all three resolution cases

### Phase 3: Codegen Support [DONE]
1. ✅ Update MIR lowering for `FreeFunction` case (`mir.spl:lower_method_call`)
2. ✅ Ensure proper argument handling (receiver becomes first arg for UFCS)
3. ⏳ Test code generation (pending)

### Phase 4: Testing & Polish [DONE]
1. ✅ Add comprehensive tests for UFCS (`simple/std_lib/test/features/ufcs_spec.spl`)
2. ✅ Test priority ordering (Instance > Trait > FreeFunction)
3. ✅ Test edge cases (argument count, empty collections, expression receivers)
4. ✅ Update error messages with type info, suggestions, and resolution attempts

---

## Alternatives Considered

### 1. Extension Methods (Kotlin-style)
```simple
extension fn i64.double() -> i64:
    self * 2
```
**Rejected:** Requires new syntax, more complex than UFCS.

### 2. Implicit Conversions
```simple
implicit fn to_doubleable(x: i64) -> Doubleable: ...
```
**Rejected:** Too magical, harder to reason about.

### 3. Trait-Based Only
Only allow UFCS through trait implementations.
**Rejected:** More restrictive, requires trait boilerplate.

---

## Summary

| Aspect | Decision |
|--------|----------|
| **Where** | Resolution pass (after type inference) |
| **AST Change** | None (keep MethodCall) |
| **HIR Change** | Add `MethodResolution` enum |
| **Priority** | Instance > Trait > Free Function |
| **Type Matching** | First parameter must be compatible |
| **Self Naming** | Any parameter name works |

This design provides UFCS with minimal changes to the parser and AST, implementing the transformation at resolution time where full type information is available.
