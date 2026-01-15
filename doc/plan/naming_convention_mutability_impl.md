# Implementation Plan: Naming Convention Mutability

## Overview

Implement a naming convention system where variable mutability is determined by the variable name pattern instead of explicit keywords.

**Research Document:** `doc/research/naming_convention_mutability.md`

---

## Feature Summary

| Name Pattern | Category | Behavior |
|--------------|----------|----------|
| `CONSTANT` | Constant | Immutable, non-rebindable, compile-time |
| `TypeName` | Type | Reserved for class/struct/enum names |
| `variable` | Immutable | Immutable, supports `->` functional update |
| `variable_` | Mutable | Mutable, supports reassignment and `->` |
| `_private` | Private | Private member (prefix), mutability by suffix |

---

## Implementation Phases

### Phase 1: Lexer Updates

**Goal:** Recognize naming patterns during tokenization.

**Tasks:**

1. Add `NamePattern` enum:
   ```rust
   pub enum NamePattern {
       Constant,      // ALL_CAPS
       TypeName,      // PascalCase
       Immutable,     // lowercase
       Mutable,       // ends with _
       Private,       // starts with _
   }
   ```

2. Update `Token::Identifier` to include pattern:
   ```rust
   Identifier {
       name: String,
       pattern: NamePattern,
   }
   ```

3. Implement pattern detection in lexer:
   ```rust
   fn detect_name_pattern(name: &str) -> NamePattern {
       if name.chars().all(|c| c.is_uppercase() || c == '_') {
           NamePattern::Constant
       } else if name.ends_with('_') {
           NamePattern::Mutable
       } else if name.starts_with('_') {
           NamePattern::Private
       } else if name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
           NamePattern::TypeName
       } else {
           NamePattern::Immutable
       }
   }
   ```

**Files:**
- `src/parser/src/lexer.rs`
- `src/parser/src/token.rs`

---

### Phase 2: Parser Updates

**Goal:** Parse variable declarations without `val`/`var` keywords.

**Tasks:**

1. Update variable declaration parsing:
   ```simple
   # Old syntax (still supported for compatibility)
   val x = 5
   var y = 0

   # New syntax (inferred from name)
   x = 5       # Immutable (lowercase)
   y_ = 0      # Mutable (underscore suffix)
   MAX = 100   # Constant (ALL_CAPS)
   ```

2. Distinguish assignment from declaration:
   - First occurrence of name = declaration
   - Subsequent occurrences = assignment (if mutable)

3. Handle type annotations:
   ```simple
   x: i32 = 5           # Immutable with type
   y_: i32 = 0          # Mutable with type
   MAX: i32 = 100       # Constant with type
   ```

4. Update AST `VarDecl`:
   ```rust
   pub struct VarDecl {
       pub name: String,
       pub pattern: NamePattern,  // NEW
       pub type_annotation: Option<Type>,
       pub initializer: Expr,
       pub span: Span,
   }
   ```

**Files:**
- `src/parser/src/statements/mod.rs`
- `src/parser/src/ast/nodes/core.rs`

---

### Phase 3: Semantic Analysis

**Goal:** Enforce mutability rules based on naming patterns.

**Tasks:**

1. Add mutability checking pass:
   ```rust
   fn check_assignment(&self, target: &Expr, span: Span) -> Result<()> {
       match target.name_pattern() {
           NamePattern::Constant => {
               Err(Error::CannotAssignToConstant(span))
           }
           NamePattern::Immutable => {
               Err(Error::CannotReassignImmutable(span))
           }
           NamePattern::Mutable | NamePattern::Private => Ok(()),
           NamePattern::TypeName => {
               Err(Error::CannotAssignToType(span))
           }
       }
   }
   ```

2. Validate functional update (`->`) usage:
   ```rust
   fn check_functional_update(&self, target: &Expr, span: Span) -> Result<()> {
       match target.name_pattern() {
           NamePattern::Constant => {
               Err(Error::CannotFunctionalUpdateConstant(span))
           }
           NamePattern::TypeName => {
               Err(Error::CannotFunctionalUpdateType(span))
           }
           _ => Ok(()),  // Allowed on immutable and mutable
       }
   }
   ```

3. Add error messages:
   ```
   error[E0501]: cannot reassign to immutable variable `counter`
     --> src/main.spl:10:5
      |
   10 |     counter = 5
      |     ^^^^^^^^^^^ cannot assign twice to immutable variable
      |
      = help: consider using `counter_` for a mutable variable

   error[E0502]: cannot assign to constant `MAX_SIZE`
     --> src/main.spl:15:5
      |
   15 |     MAX_SIZE = 200
      |     ^^^^^^^^^^^^^^ constants cannot be reassigned
   ```

**Files:**
- `src/compiler/src/hir/lower.rs`
- `src/compiler/src/hir/types.rs`

---

### Phase 4: Functional Update Operator (`->`)

**Goal:** Implement the `->` operator for immutable rebinding.

**Tasks:**

1. Parse `->` expressions:
   ```simple
   counter->increment()           # Method call rebind
   counter->value = value + 1     # Field update rebind
   ```

2. Desugar to assignment:
   ```rust
   // counter->increment()
   // Desugars to:
   // counter = counter.increment()

   // counter->value = counter.value + 1
   // Desugars to:
   // counter = Counter(value: counter.value + 1, ...spread)
   ```

3. Handle chaining:
   ```simple
   list->filter(f)->map(g)->sort()
   # Desugars to:
   # list = list.filter(f)
   # list = list.map(g)
   # list = list.sort()
   ```

4. Handle tuple returns:
   ```simple
   result = counter->pop()
   # When pop() returns (Self, T), desugars to:
   # (counter, result) = counter.pop()
   ```

**Files:**
- `src/parser/src/expressions/postfix.rs`
- `src/compiler/src/interpreter.rs`
- `src/compiler/src/mir/lower.rs`

---

### Phase 5: `self` Return Type

**Goal:** Allow `self` as a return type with implicit return.

**Tasks:**

1. Add `Type::SelfType` variant:
   ```rust
   pub enum Type {
       // ... existing variants
       SelfType,  // NEW: represents the implementing type
   }
   ```

2. Parse `-> self` return type:
   ```simple
   impl Counter:
       fn increment() -> self:
           self->value = self.value + 1
           # Implicit return of self
   ```

3. Type-check `self` return type:
   - Resolve `self` to the implementing struct type
   - Verify return value matches

4. Insert implicit return:
   ```rust
   fn lower_method_body(&mut self, body: &Block, returns_self: bool) -> MirBlock {
       let lowered = self.lower_block(body);
       if returns_self && !body.has_explicit_return() {
           // Insert: return self
           lowered.push(MirInst::Return(MirValue::Self));
       }
       lowered
   }
   ```

**Files:**
- `src/parser/src/ast/nodes/core.rs`
- `src/parser/src/types_def/mod.rs`
- `src/compiler/src/hir/lower.rs`

---

### Phase 6: Migration & Compatibility

**Goal:** Support both old and new syntax during transition.

**Tasks:**

1. Keep `val`/`var` keywords working:
   ```simple
   # Both syntaxes valid:
   val x = 5          # Explicit keyword
   x = 5              # Inferred from name

   var y = 0          # Explicit keyword
   y_ = 0             # Inferred from name
   ```

2. Add deprecation warnings:
   ```
   warning: `val` keyword is redundant for lowercase variable `x`
     --> src/main.spl:5:5
      |
    5 |     val x = 5
      |     ^^^ help: remove `val` keyword
   ```

3. Add migration tool:
   ```bash
   simple migrate --naming-convention src/
   ```

**Files:**
- `src/parser/src/statements/mod.rs`
- `simple/app/migrate/`

---

## Test Plan

### Unit Tests

1. Lexer pattern detection
2. Parser variable declarations
3. Semantic analysis mutability checking
4. Functional update desugaring
5. Self return type resolution

### Integration Tests

1. End-to-end variable declaration and usage
2. Functional update with method chaining
3. Error messages for invalid assignments
4. Migration tool correctness

### SSpec Tests

See `simple/std_lib/test/features/naming_convention/naming_convention_spec.spl`

---

## Dependencies

- Functional update operator (`->`) - partially implemented
- HIR/MIR infrastructure - complete
- Error recovery system - complete

---

## Risks

1. **Breaking changes** - existing code using `val`/`var` needs migration
2. **Parsing ambiguity** - `x = 5` could be declaration or assignment
3. **IDE support** - need to update syntax highlighting

---

## Milestones

1. **M1: Lexer & Parser** - Pattern detection, declaration parsing
2. **M2: Semantic Analysis** - Mutability enforcement
3. **M3: Functional Update** - `->` operator implementation
4. **M4: Self Type** - `-> self` return type
5. **M5: Migration** - Tool and deprecation warnings

---

## References

- Research: `doc/research/naming_convention_mutability.md`
- Implicit Self Grammar: `doc/research/implicit_self_grammar.md`
- Functional Update Status: `vulkan-backend/doc/status/functional_update.md`
