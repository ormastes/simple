# Error Catalog Phase 3 - Remaining Integration Work

**Status:** Ready to implement
**Prerequisites:** ✅ Phase 1 & 2 Complete
**Estimated Effort:** 3-5 days

---

## Overview

Phase 1 (catalog design & tests) and Phase 2 (infrastructure) are complete. **Phase 3** involves integrating the 84 new error codes into the actual compiler by adding detection logic and error emission at appropriate points.

---

## Phase 3A: Semantic Analyzer Integration

**Goal:** Emit E1011-E1080 during semantic analysis

### E1011-E1018: Basic Semantic Errors (8 codes)

**Files to modify:**
- `src/compiler/src/hir/lower/type_resolution.rs`
- `src/compiler/src/hir/lower/name_resolution.rs`

**Tasks:**
1. **E1011 (Undefined Type):** Add check when resolving type references
2. **E1012 (Undefined Field):** Check field access in struct operations
3. **E1013 (Unknown Method):** Validate method calls
4. **E1014 (Unknown Class):** Check class references
5. **E1015 (Unknown Enum):** Check enum references
6. **E1016 (Let Binding Failed):** Validate let binding initialization
7. **E1017 (Impure Function in Contract):** Check contract purity
8. **E1018 (Effect Declaration Failed):** Validate effect declarations

**Example implementation:**
```rust
// E1011 - Undefined Type
fn resolve_type(&mut self, type_ref: &TypeRef) -> Result<Type, CompileError> {
    let type_name = &type_ref.name;

    if !self.type_env.contains(type_name) {
        let ctx = ErrorContext::new()
            .with_span(type_ref.span)
            .with_code(codes::UNDEFINED_TYPE)
            .with_help(self.suggest_similar_type(type_name));

        return Err(CompileError::semantic_with_context(
            format!("type `{}` not found in this scope", type_name),
            ctx
        ));
    }

    Ok(self.type_env.get(type_name))
}
```

### E1019-E1031: Pattern Matching & Traits (13 codes)

**Files to modify:**
- `src/compiler/src/hir/lower/pattern_matching.rs`
- `src/compiler/src/type_check/trait_resolution.rs`

**Tasks:**
1. **E1019 (Duplicate Binding):** Check pattern bindings for duplicates
2. **E1020 (Argument Count Mismatch):** Validate function call arguments
3. **E1021 (Missing Struct Fields):** Check struct literal completeness
4. **E1022 (Invalid LHS Assignment):** Validate assignment targets
5. **E1023 (Invalid Struct Literal):** Check struct construction
6. **E1024 (Const Eval Failed):** Handle const evaluation failures
7. **E1025 (Duplicate Method):** Check for method redefinition
8. **E1026-E1028 (Associated Types):** Validate trait associated types
9. **E1029 (Conflicting Trait Bounds):** Check trait bound conflicts
10. **E1030 (Invalid Lifetime on Trait):** Validate trait lifetimes
11. **E1031 (Missing Trait Method):** Check trait implementation completeness

### E1032-E1040: Visibility & Self (9 codes)

**Files to modify:**
- `src/compiler/src/hir/lower/visibility_check.rs`
- `src/compiler/src/hir/lower/self_resolution.rs`

**Tasks:**
1. **E1032 (Self in Static):** Detect `self` in static methods
2. **E1033 (Invalid Self Import):** Check self import validity
3. **E1034 (Unresolved Import):** Validate import paths
4. **E1035 (Invalid Self Context):** Check `self` usage context
5. **E1036 (Closure Capture Failed):** Validate closure captures
6. **E1037 (Invalid Self Param):** Check self parameter validity
7. **E1038 (Private in Public):** Check visibility leaks
8. **E1039 (Invalid Visibility):** Validate visibility modifiers
9. **E1040 (Private Field Access):** Check field access permissions

### E1041-E1057: Type Operations & Coercion (17 codes)

**Files to modify:**
- `src/compiler/src/semantics/type_coercion.rs` (already exists)
- `src/compiler/src/type_check/operations.rs`

**Tasks:**
1. **E1041 (Invalid Unary Op):** Check unary operator type compatibility
2. **E1042 (Invalid Self Type):** Validate `Self` type usage
3. **E1043 (Invalid Index Type):** Check array index types
4. **E1044 (Tuple Index OOB):** Validate tuple index bounds
5. **E1045 (Invalid Field Assign):** Check field assignment validity
6. **E1046-E1047 (Field Access):** Validate field access permissions
7. **E1048-E1049 (Callability):** Check if types are callable
8. **E1050 (Disallowed Coercion):** Prevent implicit type coercion
9. **E1051 (Closure Signature Mismatch):** Validate closure types
10. **E1052 (Invalid Let-Else Pattern):** Check let-else patterns
11. **E1053 (Cannot Borrow Immutable):** Check mutability
12. **E1054 (Invalid Dereference):** Validate dereference operations
13. **E1055 (Type Alias Bounds):** Check type alias constraints
14. **E1056 (Invalid Range):** Validate range expressions
15. **E1057 (Yield Outside Generator):** Check yield context

### E1058-E1080: Advanced Features (23 codes)

**Files to modify:**
- `src/compiler/src/hir/lower/attributes.rs`
- `src/compiler/src/type_check/intrinsics.rs`
- `src/compiler/src/type_check/generics.rs`

**Tasks:**
1. **E1058 (Invalid Doc Comment):** Check doc comment placement
2. **E1059 (Invalid Implicit Deref):** Validate auto-deref
3. **E1060 (Invalid Const Expression):** Check const contexts
4. **E1061 (Empty Enum):** Validate enum has variants
5. **E1062 (Recursion Limit):** Check compilation recursion
6. **E1063 (Type Size Limit):** Validate type sizes
7. **E1064-E1065 (Intrinsic Types):** Check intrinsic type compatibility
8. **E1066 (Invalid Main Signature):** Validate main function
9. **E1067 (Invalid Builtin Attribute):** Check attribute usage
10. **E1068-E1069 (Bindings):** Validate binding consistency
11. **E1070 (Invalid Default Variant):** Check default variant uniqueness
12. **E1071 (Invalid Attribute Position):** Validate attribute placement
13. **E1072 (Invalid Destructuring):** Check destructuring patterns
14. **E1073 (Non-Exhaustive Type):** Check type construction
15. **E1074 (Conflicting Representation):** Validate repr attributes
16. **E1075 (Discriminant Overflow):** Check enum discriminants
17. **E1076-E1078 (Intrinsics):** Validate intrinsic usage
18. **E1079 (Missing Generic Arguments):** Check generic parameters
19. **E1080 (Type Too Complex):** Validate type complexity

**Estimated:** 2-3 days

---

## Phase 3B: Parser Integration

**Goal:** Emit E0013-E0016 during parsing

**Files to modify:**
- `src/parser/src/pattern_parser.rs`
- `src/parser/src/literal_parser.rs`
- `src/parser/src/attribute_parser.rs`

**Tasks:**
1. **E0013 (Invalid Range Pattern):** Detect malformed range patterns like `1...10` or `x..`
2. **E0014 (Invalid Literal Pattern):** Check for invalid literals in patterns
3. **E0015 (Unterminated Attribute):** Detect unclosed `#[attr` blocks
4. **E0016 (Expected Item):** Report when item definition is expected but missing

**Example implementation:**
```rust
// E0013 - Invalid Range Pattern
fn parse_range_pattern(&mut self) -> ParseResult<Pattern> {
    let start = self.parse_expr()?;

    if !self.consume_if(Token::DotDot) && !self.consume_if(Token::DotDotEq) {
        return Err(self.error_with_code(
            codes::INVALID_RANGE_PATTERN,
            "invalid range in pattern",
            self.current_span()
        ));
    }

    let end = self.parse_expr()?;
    Ok(Pattern::Range(start, end))
}
```

**Estimated:** 0.5 days

---

## Phase 3C: Control Flow Validation

**Goal:** Emit E1104-E1105 for control flow errors

**Files to modify:**
- `src/compiler/src/hir/lower/control_flow.rs`

**Tasks:**
1. **E1104 (Return in Closure):** Detect `return` statements in closures
2. **E1105 (Invalid Control Flow):** Catch other invalid control flow

**Example implementation:**
```rust
// E1104 - Return in Closure
fn check_return_in_closure(&self, stmt: &Stmt, in_closure: bool) -> Result<(), CompileError> {
    if in_closure && matches!(stmt, Stmt::Return(_)) {
        let ctx = ErrorContext::new()
            .with_span(stmt.span())
            .with_code(codes::RETURN_IN_CLOSURE)
            .with_help("closures should use implicit return or use a different control flow");

        return Err(CompileError::semantic_with_context(
            "`return` cannot be used in closure context",
            ctx
        ));
    }
    Ok(())
}
```

**Estimated:** 0.5 days

---

## Phase 3D: Capability System Integration

**Goal:** Emit E1301-E1302 for capability violations

**Files to modify:**
- `src/compiler/src/capability/checker.rs` (may need to create)
- `src/compiler/src/type_check/capability_check.rs`

**Tasks:**
1. **E1301 (Capability Violation):** Detect mutation through immutable capability
2. **E1302 (Isolation Violation):** Detect aliasing of `iso` references

**Example implementation:**
```rust
// E1301 - Capability Violation
fn check_mutation(&self, expr: &Expr, cap: Capability) -> Result<(), CompileError> {
    if matches!(cap, Capability::Immutable) && expr.is_mutating_operation() {
        let ctx = ErrorContext::new()
            .with_span(expr.span())
            .with_code(codes::CAPABILITY_VIOLATION)
            .with_note("operation requires `mut` capability")
            .with_help("use `mut` capability or change the operation");

        return Err(CompileError::semantic_with_context(
            "trying to mutate through immutable capability",
            ctx
        ));
    }
    Ok(())
}
```

**Estimated:** 1 day

---

## Phase 3E: Codegen Integration

**Goal:** Emit E2003-E2009 during code generation

**Files to modify:**
- `src/compiler/src/codegen/instr/*.rs`
- `src/compiler/src/codegen/builder.rs`

**Tasks:**
1. **E2003 (Failed Build Load):** Report IR load instruction failures
2. **E2004 (Failed Build Store):** Report IR store instruction failures
3. **E2005 (Failed Build Alloca):** Report IR alloca failures
4. **E2006 (Failed Build Call):** Report IR call instruction failures
5. **E2007 (Failed to Cast):** Report incompatible type casts
6. **E2008 (Failed Build GEP):** Report GEP instruction failures
7. **E2009 (Unsupported Return Type):** Report unsupported return types

**Example implementation:**
```rust
// E2007 - Failed to Cast
fn build_cast(&mut self, from: Type, to: Type, span: Span) -> Result<Value, CompileError> {
    if !can_cast(&from, &to) {
        let ctx = ErrorContext::new()
            .with_span(span)
            .with_code(codes::FAILED_TO_CAST)
            .with_help("check if the types are compatible for this cast");

        return Err(CompileError::codegen_with_context(
            format!("failed to cast from `{}` to `{}`", from, to),
            ctx
        ));
    }

    // Build cast instruction
    Ok(self.builder.build_cast(from, to))
}
```

**Estimated:** 1 day

---

## Phase 3F: Runtime Integration

**Goal:** Emit E3006-E3009 during execution

**Files to modify:**
- `src/runtime/src/executor/*.rs`
- `src/compiler/src/interpreter/node_exec.rs`

**Tasks:**
1. **E3006 (Await Failed):** Report failed async operations
2. **E3007 (Promise Rejected):** Report promise rejections
3. **E3008 (Function Not Found):** Report missing functions at runtime
4. **E3009 (Method Not Found):** Report missing methods at runtime

**Example implementation:**
```rust
// E3008 - Function Not Found
fn call_by_name(&self, name: &str) -> Result<Value, RuntimeError> {
    if !self.functions.contains_key(name) {
        return Err(RuntimeError::with_code(
            codes::FUNCTION_NOT_FOUND,
            format!("function `{}` not found", name)
        ));
    }

    let func = self.functions.get(name).unwrap();
    func.call(&[])
}
```

**Estimated:** 0.5 days

---

## Phase 3G: FFI Safety Check

**Goal:** Emit E4005 for FFI type safety violations

**Files to modify:**
- `src/compiler/src/ffi/type_check.rs` (may need to create)
- `src/compiler/src/hir/lower/ffi.rs`

**Tasks:**
1. **E4005 (Type Not FFI-Safe):** Check FFI function signatures for unsafe types

**Example implementation:**
```rust
// E4005 - Type Not FFI-Safe
fn check_ffi_type(&self, ty: &Type, span: Span) -> Result<(), CompileError> {
    if !ty.is_ffi_safe() {
        let ctx = ErrorContext::new()
            .with_span(span)
            .with_code(codes::TYPE_NOT_FFI_SAFE)
            .with_help("use only FFI-compatible types (integers, floats, pointers) in FFI signatures");

        return Err(CompileError::semantic_with_context(
            format!("type `{}` is not FFI-safe", ty),
            ctx
        ));
    }
    Ok(())
}
```

**Estimated:** 0.5 days

---

## Phase 3H: Testing & Validation

**Goal:** Ensure all error codes work correctly

**Tasks:**
1. Run all 95 SSpec tests
2. Verify error messages match expected format
3. Test Korean translations appear correctly
4. Add integration tests for error emission
5. Update error explanations with examples
6. Verify help text is useful

**Files to create/modify:**
- `src/compiler/tests/error_emission_tests.rs`
- `src/compiler/src/error_explanations.rs` (update with examples)

**Estimated:** 1 day

---

## Implementation Strategy

### Recommended Order

1. **Start with high-impact errors** (E1020, E1050, E3001, E3002)
2. **Group related errors** (implement all pattern matching errors together)
3. **Test incrementally** (run SSpec tests after each group)
4. **Update documentation** as you implement

### Checklist per Error Code

- [ ] Find appropriate detection point in codebase
- [ ] Add error emission with `ErrorContext` and proper code
- [ ] Extract context variables for i18n (already done in Phase 2)
- [ ] Run corresponding SSpec test
- [ ] Verify error message appears correctly
- [ ] Test Korean translation
- [ ] Add example to error explanation
- [ ] Document any edge cases

---

## Estimated Total Effort

| Phase | Effort | Priority |
|-------|--------|----------|
| 3A: Semantic (70 codes) | 2-3 days | High |
| 3B: Parser (4 codes) | 0.5 day | Medium |
| 3C: Control Flow (2 codes) | 0.5 day | Medium |
| 3D: Capability (2 codes) | 1 day | High |
| 3E: Codegen (7 codes) | 1 day | Medium |
| 3F: Runtime (4 codes) | 0.5 day | Medium |
| 3G: FFI (1 code) | 0.5 day | Low |
| 3H: Testing | 1 day | High |
| **Total** | **7-9 days** | |

---

## Success Criteria

- [ ] All 95 SSpec tests passing
- [ ] All 84 new error codes emitted correctly
- [ ] Korean translations display properly
- [ ] Error messages are helpful and actionable
- [ ] No regressions in existing error handling
- [ ] Documentation complete with examples

---

## Notes

- **Don't rush:** Quality error messages are worth the investment
- **Test frequently:** Run SSpec tests after each group of errors
- **User perspective:** Write error messages from user's perspective
- **Examples matter:** Good examples in help text save debugging time
- **Consistency:** Follow existing error message patterns

---

## After Phase 3

Once integration is complete:

1. **Update changelog** with new error codes
2. **Create migration guide** for common errors
3. **Add error index** to documentation
4. **Consider error recovery** strategies
5. **Gather user feedback** on error quality
