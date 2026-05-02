# Flow-Sensitive Type Narrowing (Smart Casts) -- Design Document

**Status:** PROPOSAL
**Date:** 2026-02-24
**Author:** Generated via research of compiler codebase

---

## 1. Motivation

Simple currently requires explicit unwrapping of optional types and has no way to automatically narrow union types after type checks. This leads to repetitive, verbose code:

```simple
fn process(x: i64?):
    if x.?:
        # x is still i64? here -- must manually unwrap
        print x.unwrap() + 1

fn handle(value: i64 | text):
    match value:
        case i64: print value + 1          # match arms already narrow, but if/else does not
        case text: print value.len()
```

TypeScript, Kotlin, and Swift all provide flow-sensitive narrowing where a type check in a conditional automatically refines the type of the checked variable in the branches that follow. This design proposes adding the same capability to Simple.

---

## 2. Narrowing Triggers

The following conditions will trigger type narrowing:

### 2.1. Nil/Optional checks (`!= nil`, `.?`)

The most common case. After checking that an optional is non-nil, the variable's type is narrowed from `T?` to `T`.

```simple
fn process(x: i64?):
    if x != nil:
        # x narrowed to i64
        print x + 1

    if x.?:
        # x narrowed to i64
        print x + 1
```

The negated form also narrows in the else branch:

```simple
fn process(x: i64?):
    if x == nil:
        return
    # After early return, x narrowed to i64 for rest of function
    print x + 1
```

### 2.2. `is` type checks

The `is` operator already exists in the parser (`KwIs` token, `HirBinOp.Is`) and is lowered to HIR. Currently it only produces a `bool` result. With narrowing, it will also refine the variable's type.

```simple
fn process(x: i64 | text):
    if x is text:
        # x narrowed to text
        print x.len()
    else:
        # x narrowed to i64
        print x + 1
```

### 2.3. `if val` pattern binding (already works, extend)

`if val` already binds a new variable with a narrowed type. This is complementary to, not replaced by, flow narrowing. The difference: `if val` creates a new binding; flow narrowing changes the type of the existing binding in scope.

```simple
# Existing: creates new binding `name`
if val name = input.?:
    process(name)

# Proposed: no new binding, just narrows `input`
if input.?:
    process(input)    # input is now non-optional
```

### 2.4. `match` arm patterns

Match arms already perform a form of narrowing through pattern destructuring. This design will formalize and extend it so that the scrutinee variable itself is narrowed within each arm body.

```simple
fn describe(x: i64 | text | bool):
    match x:
        case i64:
            # x narrowed to i64
            print "number: {x + 1}"
        case text:
            # x narrowed to text
            print "string: {x.len()} chars"
        case bool:
            # x narrowed to bool
            print "flag: {x}"
```

### 2.5. Truthiness checks

Simple has well-defined truthiness rules (see `src/compiler/35.semantics/semantics/truthiness.spl`). A bare `if x:` check narrows `x` from `T?` to `T` in the then-branch (since `nil` is falsy), but NOT for other types where truthiness depends on value (e.g., `i64` where `0` is falsy).

```simple
fn process(x: text?):
    if x:
        # x narrowed to text (nil is falsy)
        print x.len()
```

### 2.6. Negated checks and `is not`

Negated conditions narrow in the else branch:

```simple
fn process(x: i64 | text):
    if x is not text:
        # x narrowed to i64
        print x + 1
    else:
        # x narrowed to text
        print x.len()
```

---

## 3. Scope Rules

### 3.1. If/else branches

Narrowing applies independently within each branch of an `if`/`elif`/`else` chain.

```simple
fn process(x: i64?):
    if x != nil:
        # x is i64 here
        use_int(x)
    else:
        # x is nil here (technically i64? but known nil)
        handle_missing()
    # After if/else: x is back to i64? (both branches merge)
```

### 3.2. Early returns (definite assignment / reachability)

If one branch of an `if` performs an early return, break, or throw, the narrowing from the condition extends to the rest of the enclosing block. This is the "type guard" pattern used heavily in Kotlin and TypeScript.

```simple
fn process(x: i64?):
    if x == nil:
        return          # Early return -- x is nil in this branch
    # x is narrowed to i64 for the rest of the function
    print x + 1
```

This requires knowing whether a block is "definitely terminating" (returns/breaks/throws on all paths). The compiler already tracks this for return type checking.

### 3.3. Logical operators (`and`, `or`)

Narrowing chains through `and`:

```simple
fn process(x: i64?, y: text?):
    if x != nil and y != nil:
        # Both x and y are narrowed
        print x + y.len()
```

For `or`, narrowing is more limited (narrowing in individual branches but not the combined result).

### 3.4. Loop bodies

Narrowing does NOT propagate into loop bodies from outer conditions, because the loop may execute with different values on different iterations (for `var` bindings). For `val` bindings, narrowing is safe because the value cannot change.

### 3.5. Closures

Narrowing does NOT propagate into closures/lambdas, because the closure may be invoked later when the narrowing condition no longer holds (for `var` bindings). For `val` bindings, narrowing could be safe, but we defer this to a later phase for simplicity.

---

## 4. Soundness: Only Narrow Immutable Bindings

Following Kotlin's approach, flow-sensitive narrowing is only sound for immutable (`val`) bindings. A mutable (`var`) variable could be reassigned between the check and the use, invalidating the narrowing.

```simple
var x: i64? = Some(42)
if x != nil:
    # UNSAFE to narrow: another thread or a called function could set x = nil
    # For var, the compiler should NOT narrow (or should require explicit unwrap)
    pass_dn

val y: i64? = Some(42)
if y != nil:
    # SAFE to narrow: y cannot be reassigned
    print y + 1    # y is i64
```

**Exception:** Local `var` bindings that are NOT captured by any closure and NOT modified between the check and use site could potentially be narrowed. This is a more advanced analysis that can be deferred to a later phase.

**Implementation:** The `Symbol` struct in `src/compiler/20.hir/hir_types.spl` already tracks `is_mutable: bool`, so this check is straightforward.

---

## 5. Data Structures

The following new types and structures are needed:

### 5.1. NarrowingFact

Represents a single narrowing fact -- the knowledge that a variable has a more specific type.

```simple
struct NarrowingFact:
    """A type narrowing fact: variable has a more specific type."""
    symbol: SymbolId          # The variable being narrowed
    original_type: HirType    # The original declared type
    narrowed_type: HirType    # The narrowed (more specific) type
    condition: NarrowingCondition  # What caused the narrowing
    span: Span                # Location of the narrowing check
```

### 5.2. NarrowingCondition

Describes what condition triggered the narrowing.

```simple
enum NarrowingCondition:
    """What condition triggered the narrowing."""
    NilCheck(negated: bool)          # x != nil / x == nil
    ExistsCheck                       # x.?
    IsCheck(target_type: HirType)    # x is Type
    IsNotCheck(target_type: HirType) # x is not Type
    PatternMatch(pattern: HirPattern) # match arm pattern
    Truthiness                        # bare if x: (nil eliminated)
```

### 5.3. NarrowingContext

The per-scope collection of active narrowing facts. This is a stack of scopes, similar to how the `SymbolTable` manages scopes.

```simple
class NarrowingContext:
    """Tracks type narrowing facts through control flow."""
    # Stack of narrowing scopes (push on if/match entry, pop on exit)
    scopes: [NarrowingScope]

    static fn new() -> NarrowingContext:
        NarrowingContext(scopes: [NarrowingScope.new()])

    me push_scope():
        """Push a new narrowing scope (entering if/match branch)."""
        self.scopes = self.scopes.push(NarrowingScope.new())

    me pop_scope():
        """Pop the current narrowing scope (leaving branch)."""
        if self.scopes.len() > 1:
            self.scopes = self.scopes[0:self.scopes.len() - 1]

    me add_fact(fact: NarrowingFact):
        """Add a narrowing fact to the current scope."""
        val current = self.scopes[self.scopes.len() - 1]
        current.facts = current.facts.push(fact)
        self.scopes[self.scopes.len() - 1] = current

    fn lookup(symbol: SymbolId) -> HirType?:
        """Look up the narrowed type for a symbol.

        Searches from innermost scope outward, returns the most specific
        narrowing fact found.
        """
        var i = self.scopes.len() - 1
        while i >= 0:
            val scope = self.scopes[i]
            for fact in scope.facts:
                if fact.symbol.id == symbol.id:
                    return Some(fact.narrowed_type)
            i = i - 1
        nil

struct NarrowingScope:
    """A single scope level of narrowing facts."""
    facts: [NarrowingFact]

    static fn new() -> NarrowingScope:
        NarrowingScope(facts: [])
```

### 5.4. NarrowedType (optional, for type annotations)

An optional wrapper that can annotate HIR types with narrowing information, useful for diagnostics and IDE integration.

```simple
struct NarrowedType:
    """A type that has been narrowed by flow analysis."""
    base_type: HirType        # The original type before narrowing
    narrowed_type: HirType    # The narrowed type
    reason: NarrowingCondition # Why it was narrowed
```

---

## 6. Integration Points

### 6.1. Where in the pipeline

The compilation pipeline (from `src/compiler/80.driver/driver.spl`) is:

```
Phase 1: Load sources
Phase 2: Parse (AST)
Phase 3: Lower to HIR + Method Resolution + Type Checking
Phase 4: Monomorphization
Phase 5: Mode-specific (Interpret / JIT / AOT)
```

Flow-sensitive narrowing integrates into **Phase 3**, specifically between method resolution and type checking. The recommended approach is a **new sub-pass** within Phase 3:

```
Phase 3a: Lower to HIR       (existing: hir_lowering/)
Phase 3b: Method resolution   (existing: 35.semantics/resolve.spl)
Phase 3c: Narrowing analysis  (NEW: 35.semantics/narrowing.spl)
Phase 3d: Type checking       (existing: 30.types/type_infer/)
```

However, narrowing interacts tightly with type inference (the narrowed type must be used during inference). Therefore, a cleaner approach is to integrate narrowing **directly into the type inference pass** by extending `HmInferContext`.

### 6.2. Integration with HmInferContext

The `HmInferContext` struct (in `src/compiler/30.types/type_infer.spl`) manages the type environment. Narrowing extends this by adding a `NarrowingContext`:

```simple
struct HmInferContext:
    # ... existing fields ...
    env: Dict<text, TypeScheme>
    level: i64
    next_var: i64
    subst: Substitution
    errors: [TypeInferError]
    dim_solver: DimSolver
    runtime_checks: DimCheckGenerator
    dim_check_mode: DimCheckMode
    trait_solver: TraitSolver
    function_bounds: Dict<i64, [HirTraitBound]>
    # NEW: Flow-sensitive narrowing context
    narrowing: NarrowingContext
```

### 6.3. Modified inference for `If` expressions

The `infer_expr` method for `If` in `src/compiler/30.types/type_infer/inference_expr.spl` (line 456) currently:

1. Infers and checks the condition is `bool`
2. Infers the then-branch
3. Infers the else-branch (if present)
4. Unifies the branch types

With narrowing, it becomes:

1. Infer the condition type (must be `bool`)
2. **Analyze the condition for narrowing facts**
3. **Push narrowing scope, add facts for then-branch**
4. Infer the then-branch (with narrowed types)
5. **Pop narrowing scope**
6. **Push narrowing scope, add negated facts for else-branch**
7. Infer the else-branch (with negated narrowed types)
8. **Pop narrowing scope**
9. **If one branch definitely terminates, promote narrowing facts to parent scope**
10. Unify the branch types

### 6.4. Modified variable lookup

The `lookup` method in `src/compiler/30.types/type_infer/context.spl` currently just checks the type environment. With narrowing, it should first check the narrowing context:

```simple
me lookup(name: text, span: Span) -> Result<HirType, TypeInferError>:
    # First check if there is a narrowing fact for this symbol
    val symbol_id = self.env_symbol_lookup(name)
    if symbol_id.?:
        val narrowed = self.narrowing.lookup(symbol_id.unwrap())
        if narrowed.?:
            return Ok(narrowed.unwrap())

    # Fall back to normal type environment lookup
    if self.env[name].?:
        val scheme = self.env[name]
        Ok(self.instantiate(scheme))
    else:
        Err(TypeInferError.Undefined(name, span))
```

### 6.5. Match expression narrowing

The `infer_pattern` method (in `inference_control.spl`, line 518) already binds pattern variables to expected types. Narrowing extends this so that the scrutinee variable itself is also narrowed within each match arm.

### 6.6. Interaction with `ExistsCheck` (`.?`)

The `ExistsCheck` HIR node (defined in `src/compiler/20.hir/hir_definitions.spl` line 354) currently produces an `Optional` type. When used as a condition in an `if`, it should also generate a narrowing fact that removes the optional wrapper.

### 6.7. Interaction with the `is` binary operator

The `Is` / `IsNot` variants of `HirBinOp` (defined in `hir_definitions.spl`, lines 528-529) are currently parsed and lowered but produce only a `bool` result (see `expr_infer_ops.spl` line 147). With narrowing:

- `x is Type` produces a narrowing fact that `x` has type `Type` in the then-branch
- `x is not Type` produces a narrowing fact for the else-branch

This requires the `is` operator to be recognized during condition analysis. The left operand must be a `Var` (direct variable reference) and the right operand a type name.

---

## 7. Condition Analysis Algorithm

The core of the narrowing system is analyzing a condition expression to extract narrowing facts.

```simple
fn analyze_condition(cond: HirExpr) -> [NarrowingFact]:
    """Analyze a condition expression to extract narrowing facts.

    Returns facts that are true when the condition evaluates to true.
    For else-branches, negate the facts.
    """
    match cond.kind:
        # x != nil  =>  x is narrowed from T? to T
        case Binary(NotEq, Var(symbol), NilLit):
            val sym_type = lookup_symbol_type(symbol)
            match sym_type.kind:
                case Optional(inner):
                    [NarrowingFact(
                        symbol: symbol,
                        original_type: sym_type,
                        narrowed_type: inner,
                        condition: NarrowingCondition.NilCheck(negated: false),
                        span: cond.span
                    )]
                case _: []

        # nil != x  =>  same as x != nil (symmetric)
        case Binary(NotEq, NilLit, Var(symbol)):
            analyze_condition(flip_binary(cond))

        # x == nil  =>  x is narrowed to nil in then-branch, T in else-branch
        case Binary(Eq, Var(symbol), NilLit):
            # This produces a "negative" fact -- used for else-branch
            [NarrowingFact(
                symbol: symbol,
                original_type: lookup_symbol_type(symbol),
                narrowed_type: nil_type(),
                condition: NarrowingCondition.NilCheck(negated: true),
                span: cond.span
            )]

        # x.?  =>  x is non-nil
        case ExistsCheck(Var(symbol)):
            val sym_type = lookup_symbol_type(symbol)
            match sym_type.kind:
                case Optional(inner):
                    [NarrowingFact(
                        symbol: symbol,
                        original_type: sym_type,
                        narrowed_type: inner,
                        condition: NarrowingCondition.ExistsCheck,
                        span: cond.span
                    )]
                case _: []

        # x is Type  =>  x has that type
        case Binary(Is, Var(symbol), type_expr):
            val target_type = resolve_type_from_expr(type_expr)
            [NarrowingFact(
                symbol: symbol,
                original_type: lookup_symbol_type(symbol),
                narrowed_type: target_type,
                condition: NarrowingCondition.IsCheck(target_type),
                span: cond.span
            )]

        # a and b  =>  combine facts from both
        case Binary(And, left, right):
            analyze_condition(left) ++ analyze_condition(right)

        # not x  =>  negate the facts
        case Unary(Not, inner):
            negate_facts(analyze_condition(inner))

        # Bare variable (truthiness check)
        case Var(symbol):
            val sym_type = lookup_symbol_type(symbol)
            match sym_type.kind:
                case Optional(inner):
                    [NarrowingFact(
                        symbol: symbol,
                        original_type: sym_type,
                        narrowed_type: inner,
                        condition: NarrowingCondition.Truthiness,
                        span: cond.span
                    )]
                case _: []

        case _: []
```

### Negation of facts

When we need the else-branch facts, we negate the then-branch facts:

- `NilCheck(negated: false)` (x != nil => x is T) negates to: x is T? (no narrowing in else)
- `IsCheck(text)` (x is text) negates to: x is the remaining union members
- `ExistsCheck` negates to: x is nil

---

## 8. Union Type Support

Simple already has union types in the core parser (`src/compiler/10.frontend/core/types.spl`, lines 470-483) with `union_type_register` and `union_type_get_members`. However, the HIR type system does not currently have an explicit `Union` variant in `HirTypeKind`.

For narrowing to work with union types (`i64 | text`), we need one of:

**Option A: Add `Union` to HirTypeKind** (recommended)

```simple
enum HirTypeKind:
    # ... existing variants ...
    Union(members: [HirType])    # NEW: union type A | B | C
```

**Option B: Encode unions as Named types with a convention**

Use existing `Named` with a special symbol ID for union types. Less clean, but avoids modifying the core type enum.

**Recommendation:** Option A is cleaner and enables proper narrowing. When `x is text` and `x: i64 | text`, the narrowed type in the then-branch is `text`, and in the else-branch it is `i64` (the remaining member).

---

## 9. Definite Termination Analysis

For early-return narrowing (Section 3.2), we need to know if a block definitely terminates. This is a standard reachability analysis:

```simple
fn definitely_terminates(block: HirBlock) -> bool:
    """Check if a block definitely does not fall through.

    A block definitely terminates if its last statement is:
    - return
    - break (in a loop context)
    - throw
    - a sub-block that definitely terminates
    - an if/match where ALL branches definitely terminate
    """
    if block.stmts.is_empty():
        return false

    val last = block.stmts[block.stmts.len() - 1]
    match last.kind:
        case Expr(Return(_)): true
        case Expr(Break(_, _)): true
        case Expr(Continue(_)): true
        case Expr(Throw(_)): true
        case Expr(If(_, then_, Some(else_))):
            definitely_terminates(then_) and definitely_terminates(else_)
        case _: false
```

---

## 10. Error Messages

Narrowing should produce clear error messages when narrowing fails or when users try to use narrowed types incorrectly:

```
error: cannot narrow mutable variable `x`
  --> src/example.spl:5:8
  |
5 |     if x != nil:
  |        ^ `x` is declared with `var` -- narrowing only works with `val`
  |
  = help: use `if val value = x: ...` to bind a narrowed copy
  = help: or declare `x` as `val` if mutation is not needed
```

```
error: type `i64` does not contain type `text`
  --> src/example.spl:5:8
  |
5 |     if x is text:
  |        ^^^^^^^^^ `x` has type `i64`, which cannot be narrowed to `text`
```

---

## 11. Implementation Plan

### Phase 1: Foundation (estimated: 2-3 days)

**Goal:** Core data structures and nil-check narrowing for `val` bindings.

Files to create:
- `src/compiler/35.semantics/narrowing.spl` -- `NarrowingFact`, `NarrowingCondition`, `NarrowingContext`, `NarrowingScope`

Files to modify:
- `src/compiler/30.types/type_infer.spl` -- Add `narrowing: NarrowingContext` field to `HmInferContext`
- `src/compiler/30.types/type_infer/context.spl` -- Initialize `NarrowingContext` in constructors
- `src/compiler/30.types/type_infer/inference_expr.spl` -- Modify `If` inference to push/pop narrowing scopes and analyze conditions for nil checks

Deliverables:
- `if x != nil:` narrows `x` from `T?` to `T` in then-branch
- `if x.?:` narrows `x` from `T?` to `T` in then-branch
- Only for `val` bindings (checked via `Symbol.is_mutable`)

### Phase 2: Early returns and `is` checks (estimated: 2-3 days)

**Goal:** Early-return narrowing and `is` type checks.

Files to modify:
- `src/compiler/35.semantics/narrowing.spl` -- Add `analyze_condition` function, `definitely_terminates` function
- `src/compiler/30.types/type_infer/inference_expr.spl` -- Handle early-return promotion of narrowing facts to parent scope
- `src/compiler/30.types/type_infer/inference_control.spl` -- Wire narrowing into block/statement inference

Deliverables:
- `if x == nil: return` narrows `x` to `T` for rest of function
- `if x is Type:` narrows `x` to `Type` in then-branch (requires union type support, or works with enum variants)

### Phase 3: Union types and `match` narrowing (estimated: 3-4 days)

**Goal:** Full union type narrowing in `if` and `match`.

Files to modify:
- `src/compiler/20.hir/hir_types.spl` -- Add `Union(members: [HirType])` to `HirTypeKind`
- `src/compiler/30.types/type_infer/core.spl` -- Add unification rules for `Union` types
- `src/compiler/30.types/type_infer/inference_control.spl` -- Narrow scrutinee in `match` arms
- `src/compiler/20.hir/hir_lowering/types.spl` -- Lower parsed union types to HIR `Union`

Deliverables:
- `x: i64 | text` with `if x is text:` narrows to `text` in then-branch and `i64` in else
- `match` on union types narrows scrutinee in each arm

### Phase 4: Logical operators and advanced patterns (estimated: 2 days)

**Goal:** Narrowing through `and`/`or` chains and nested conditions.

Files to modify:
- `src/compiler/35.semantics/narrowing.spl` -- Handle `Binary(And, ...)` and `Binary(Or, ...)` in condition analysis
- `src/compiler/30.types/type_infer/inference_expr.spl` -- Wire through logical operator handling

Deliverables:
- `if x != nil and y != nil:` narrows both `x` and `y`
- `if not (x is text):` narrows in else-branch
- `if x is not Type:` narrows correctly

### Phase 5: Diagnostics and IDE integration (estimated: 1-2 days)

**Goal:** Clear error messages and hover-type information showing narrowed types.

Files to create/modify:
- `src/compiler/35.semantics/error_formatter.spl` -- Add narrowing-related error formatting
- `src/compiler/90.tools/api.spl` -- Expose narrowing information for IDE queries

Deliverables:
- Error messages explaining why narrowing did/did not happen
- Hover information showing narrowed type at a given position

---

## 12. Relationship to Existing Features

| Existing Feature | Relationship to Narrowing |
|---|---|
| `if val x = expr.?:` | Complementary. `if val` creates a new binding; narrowing changes the existing binding's type. Both are useful. |
| `.?` (ExistsCheck) | Input to narrowing. When used as a condition, triggers nil narrowing. |
| `is` / `is not` operators | Input to narrowing. Already parsed and lowered; narrowing adds type refinement on top of the bool result. |
| `match` patterns | Already perform destructuring. Narrowing extends this to the scrutinee itself. |
| `Optional(inner)` in HirTypeKind | The primary unwrapping target for nil-check narrowing. |
| `Symbol.is_mutable` | Used to enforce val-only narrowing for soundness. |
| `ScopeKind` enum | Extended conceptually with narrowing scopes (piggy-backs on existing scope stack). |
| Borrow checker (55.borrow/) | Orthogonal. Narrowing is a type-level analysis; borrow checking is a memory-safety analysis. They do not conflict. |
| Pattern analysis (35.semantics/pattern_analysis.spl) | Could share exhaustiveness checking logic when narrowing union types in `match`. |
| Truthiness rules (35.semantics/semantics/truthiness.spl) | Used to determine when bare `if x:` can narrow optional types. |

---

## 13. Testing Strategy

### Unit tests for narrowing analysis

```simple
# test/unit/compiler/semantics/narrowing_spec.spl

describe "NarrowingContext":
    it "narrows optional to inner type on nil check":
        val ctx = NarrowingContext.new()
        val sym = SymbolId.new(1)
        val opt_type = HirType(kind: HirTypeKind.Optional(int_type), span: dummy)
        val fact = NarrowingFact(
            symbol: sym,
            original_type: opt_type,
            narrowed_type: int_type,
            condition: NarrowingCondition.NilCheck(negated: false),
            span: dummy
        )
        ctx.push_scope()
        ctx.add_fact(fact)
        ctx.lookup(sym).to_equal(Some(int_type))

    it "does not narrow across scope boundaries":
        val ctx = NarrowingContext.new()
        ctx.push_scope()
        ctx.add_fact(some_fact)
        ctx.pop_scope()
        ctx.lookup(some_fact.symbol).to_be_nil()
```

### Integration tests for end-to-end narrowing

```simple
# test/feature/usage/narrowing_spec.spl

describe "flow-sensitive narrowing":
    it "narrows optional after nil check":
        # This should compile and run without unwrap()
        val code = """
            fn add_one(x: i64?) -> i64:
                if x != nil:
                    x + 1
                else:
                    0
        """
        compile_and_check(code).to_equal(true)

    it "rejects narrowing of mutable variables":
        val code = """
            fn bad(x: i64?):
                var y: i64? = x
                if y != nil:
                    y + 1    # Should still require unwrap for var
        """
        compile_and_check(code).to_contain("cannot narrow mutable variable")
```

---

## 14. Risks and Mitigations

| Risk | Mitigation |
|---|---|
| Performance: narrowing analysis slows compilation | Narrowing context is O(1) per scope push/pop; fact lookup is O(n) where n = facts in scope (typically < 10). Profile if issues arise. |
| Soundness: narrowing a `var` that gets reassigned concurrently | Restrict to `val` bindings only (Phase 1). Extend to local `var` in later phases with escape analysis. |
| Interaction with generics: narrowing `T?` where `T` is a type parameter | Supported naturally -- `Optional(TypeParam("T"))` narrows to `TypeParam("T")`. |
| Interpreter mode limitation | The interpreter test runner only verifies file loading, not execution. Narrowing tests must verify through the type checker, not runtime behavior. |
| Union types not in HIR | Phase 3 adds `Union` to `HirTypeKind`. Until then, only optional narrowing works (Phase 1-2). |
| Chained method call bug | Workaround using intermediate variables is already established in the codebase (see HIR lowering comments). Narrowing code will follow the same pattern. |

---

## 15. Future Extensions

- **Smart casts for `var`** with escape analysis (no closure capture, no modification between check and use)
- **Contract narrowing**: `requires x != nil` in function preconditions narrows parameter types in the function body
- **Exhaustive narrowing**: warning when not all union members are handled
- **IDE narrowing display**: show narrowed type on hover (LSP integration)
- **Narrowing through function calls**: `if list.is_empty():` could narrow `list` to "known-empty" (refinement types)

---

## 16. Summary

Flow-sensitive type narrowing is a natural extension of Simple's existing type system. The key design decisions are:

1. **Val-only narrowing** for soundness (Kotlin's approach)
2. **Integrated into type inference** rather than a separate pass (modifying `HmInferContext`)
3. **Scope-based context** that mirrors the existing `SymbolTable` scope stack
4. **Condition analysis** that extracts narrowing facts from `if` conditions, `is` checks, and `.?` existence checks
5. **Early-return promotion** using definite termination analysis
6. **Five-phase implementation** starting with the highest-value case (optional nil checks) and building toward full union type narrowing
