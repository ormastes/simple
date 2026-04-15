# Error Code Quick Wins - Immediate Improvements

**Date:** 2026-01-19
**Effort:** 2-3 hours
**Impact:** High (improves 20+ common errors)

---

## Overview

This plan focuses on **immediate, low-effort improvements** that significantly enhance error quality by adding error codes and helpful suggestions to existing error creation points.

---

## Quick Win 1: Add Missing Error Codes to Factory Functions

**File:** `src/compiler/src/error.rs` (factory module)

### Changes Needed

Many factory functions create errors without setting error codes. Update them to include codes by default:

```rust
/// Error when a method is not found on a type.
pub fn method_not_found(method_name: &str, type_name: &str) -> CompileError {
    // OLD: Just creates semantic error
    // NEW: Include error code in context
    let ctx = ErrorContext::new()
        .with_code(codes::UNKNOWN_METHOD);

    CompileError::semantic_with_context(
        format!("no method named '{}' found for type '{}'", method_name, type_name),
        ctx
    )
}
```

### Functions to Update (15 functions)

1. `method_not_found()` → add `codes::UNKNOWN_METHOD`
2. `field_not_found()` → add `codes::UNDEFINED_FIELD`
3. `function_not_found()` → add `codes::UNDEFINED_FUNCTION`
4. `variable_not_found()` → add `codes::UNDEFINED_VARIABLE`
5. `type_not_found()` → add `codes::UNDEFINED_TYPE`
6. `class_not_found()` → add `codes::UNKNOWN_CLASS`
7. `enum_not_found()` → add `codes::UNKNOWN_ENUM`
8. `type_mismatch()` → add `codes::TYPE_MISMATCH`
9. `argument_count_mismatch()` → add `codes::ARGUMENT_COUNT_MISMATCH`
10. `cannot_assign_to_const()` → add `codes::INVALID_ASSIGNMENT`
11. `cannot_mutate_immutable()` → add `codes::INVALID_ASSIGNMENT`
12. `circular_dependency()` → add `codes::CIRCULAR_DEPENDENCY`
13. `duplicate_impl()` → add `codes::DUPLICATE_DEFINITION`
14. `blocking_in_async()` → add `codes::INVALID_OPERATION`
15. `side_effect_in_pure()` → add `codes::INVALID_OPERATION`

---

## Quick Win 2: Add Typo Suggestions to "Not Found" Errors

**Leverage existing `typo` module** to provide helpful suggestions.

### Pattern

```rust
// Before
pub fn variable_not_found(var_name: &str) -> CompileError {
    CompileError::Semantic(
        format!("cannot find variable '{}' in this scope", var_name)
    )
}

// After
pub fn variable_not_found(var_name: &str) -> CompileError {
    let ctx = ErrorContext::new()
        .with_code(codes::UNDEFINED_VARIABLE);

    CompileError::semantic_with_context(
        format!("cannot find variable '{}' in this scope", var_name),
        ctx
    )
}

// Better (with suggestions - requires call site to pass candidates)
pub fn variable_not_found_with_suggestions(
    var_name: &str,
    candidates: &[&str]
) -> CompileError {
    let mut ctx = ErrorContext::new()
        .with_code(codes::UNDEFINED_VARIABLE);

    if let Some(suggestion) = typo::suggest_name(var_name, candidates.iter().copied()) {
        ctx = ctx.with_help(format!("did you mean '{}'?", suggestion));
    }

    CompileError::semantic_with_context(
        format!("cannot find variable '{}' in this scope", var_name),
        ctx
    )
}
```

### Functions That Need Suggestion Variants (8 functions)

1. `variable_not_found_with_suggestions()`
2. `function_not_found_with_suggestions()`
3. `type_not_found_with_suggestions()`
4. `method_not_found_with_suggestions()`
5. `field_not_found_with_suggestions()`
6. `class_not_found_with_suggestions()`
7. `enum_not_found_with_suggestions()`
8. `unknown_macro_with_suggestions()`

---

## Quick Win 3: Enhance Existing Error Usage

### File: `src/compiler/src/interpreter_call/builtins.rs`

**Current:** Uses INVALID_CONTEXT in 4 places without helpful messages

**Improvement:**

```rust
// Before
.with_code(codes::INVALID_CONTEXT)

// After
.with_code(codes::INVALID_CONTEXT)
.with_help("recv() must be called within an actor context")
.with_note("consider using spawn_actor {} to create actor context")
```

**Changes (4 locations):**
- Line 136: Add help about actor spawn context
- Line 144: Add note about mailbox requirements
- Line 199: Add help about sender requirements

### File: `src/compiler/src/interpreter_method/collections.rs`

**Current:** Uses TYPE_MISMATCH 5 times without specific context

**Improvement:**

```rust
// Line 65: Array/List append
.with_code(codes::TYPE_MISMATCH)
.with_help("append() expects an element of the same type as the list")

// Line 260: Hashmap key type
.with_code(codes::TYPE_MISMATCH)
.with_help("all keys in a hashmap must have the same type")

// Line 529: Filter predicate
.with_code(codes::TYPE_MISMATCH)
.with_help("filter() expects a function that returns a boolean")
```

---

## Quick Win 4: Add Missing Concurrency Error Codes

### File: `src/compiler/src/interpreter_call/builtins.rs`

**Add E1203 - Channel Closed:**

```rust
// Around line 150 (in recv implementation)
if let Some(Value::Channel(ch)) = args.get(0) {
    let mut ch_guard = ch.lock().unwrap();

    // ADD THIS CHECK
    if ch_guard.is_closed {
        let ctx = ErrorContext::new()
            .with_code(codes::CHANNEL_CLOSED)
            .with_help("check if another task closed this channel");

        return Err(CompileError::runtime_with_context(
            "cannot receive from closed channel",
            ctx
        ));
    }

    // ... existing code
}
```

**Add E1204 - Deadlock Detection** (if cycle detection exists):

```rust
// When detecting circular wait in actor message passing
if self.detect_circular_wait() {
    let ctx = ErrorContext::new()
        .with_code(codes::DEADLOCK_DETECTED)
        .with_note("circular dependency detected in message passing")
        .with_help("restructure actor communication to avoid cycles");

    return Err(CompileError::runtime_with_context(
        "potential deadlock: circular wait condition detected",
        ctx
    ));
}
```

---

## Quick Win 5: Update I18n Conversions (High Priority Errors)

### File: `src/compiler/src/i18n_diagnostics.rs`

Add conversions for commonly-used error codes that are missing:

```rust
// Add after line 100
codes::UNKNOWN_METHOD => {
    let (method_name, type_name) = extract_method_info(message);
    let msg_ctx = ctx2("method", method_name, "type", type_name);
    I18nDiagnostic::error_i18n("compiler", "E1013", &msg_ctx)
}

codes::UNKNOWN_CLASS => {
    let name = extract_name_from_message(message);
    let msg_ctx = ctx1("name", name);
    I18nDiagnostic::error_i18n("compiler", "E1014", &msg_ctx)
}

codes::UNKNOWN_ENUM => {
    let name = extract_name_from_message(message);
    let msg_ctx = ctx1("name", name);
    I18nDiagnostic::error_i18n("compiler", "E1015", &msg_ctx)
}

codes::ARGUMENT_COUNT_MISMATCH => {
    let (expected, found) = extract_count_mismatch(message);
    let msg_ctx = ctx2("expected", expected, "found", found);
    I18nDiagnostic::error_i18n("compiler", "E1020", &msg_ctx)
}

codes::INVALID_CONTEXT => {
    let msg_ctx = ctx1("message", message);
    I18nDiagnostic::error_i18n("compiler", "E1081", &msg_ctx)
}

codes::ACTOR_JOIN_FAILED => {
    let msg_ctx = ctx1("message", message);
    I18nDiagnostic::error_i18n("compiler", "E1205", &msg_ctx)
}

codes::CHANNEL_CLOSED => {
    let msg_ctx = ctx1("message", message);
    I18nDiagnostic::error_i18n("compiler", "E1203", &msg_ctx)
}

codes::DEADLOCK_DETECTED => {
    let msg_ctx = ctx1("message", message);
    I18nDiagnostic::error_i18n("compiler", "E1204", &msg_ctx)
}
```

**Total:** 8 new conversions (15 minutes)

---

## Implementation Checklist

### Phase 1: Error Factory Updates (1 hour)
- [ ] Update 15 factory functions to include error codes
- [ ] Add 8 new `_with_suggestions()` variant functions
- [ ] Test compilation: `cargo check -p simple-compiler`

### Phase 2: Usage Site Improvements (30 minutes)
- [ ] Update `builtins.rs` INVALID_CONTEXT usage (4 locations)
- [ ] Update `collections.rs` TYPE_MISMATCH usage (5 locations)
- [ ] Test compilation: `cargo check -p simple-compiler`

### Phase 3: I18n Conversions (30 minutes)
- [ ] Add 8 high-priority i18n conversions
- [ ] Test i18n: `cargo test -p simple-compiler i18n`
- [ ] Verify Korean translations load correctly

### Phase 4: Concurrency Errors (30 minutes)
- [ ] Add E1203 channel closed check
- [ ] Add E1204 deadlock detection (if applicable)
- [ ] Test: `cargo test -p simple-compiler actor`

### Phase 5: Validation (30 minutes)
- [ ] Run full test suite: `cargo test --workspace`
- [ ] Run sample error cases manually
- [ ] Verify error messages improved
- [ ] Check Korean translation works

---

## Expected Results

### Before
```
error: cannot find variable 'coun' in this scope
```

### After
```
error[E1001]: cannot find variable 'coun' in this scope
  --> test.spl:5:10
   |
5  |     print coun
   |           ^^^^ not found in this scope
   |
help: did you mean 'count'?
```

### In Korean
```
오류[E1001]: 변수 'coun'을(를) 이 범위에서 찾을 수 없습니다
  --> test.spl:5:10
   |
5  |     print coun
   |           ^^^^ 범위에서 찾을 수 없음
   |
도움말: 'count'을(를) 의미하셨나요?
```

---

## Files to Modify Summary

1. `src/compiler/src/error.rs` - Factory function updates
2. `src/compiler/src/i18n_diagnostics.rs` - Add 8 conversions
3. `src/compiler/src/interpreter_call/builtins.rs` - Enhance 6 locations
4. `src/compiler/src/interpreter_method/collections.rs` - Enhance 5 locations

**Total:** 4 files, ~40 changes, 2-3 hours work

---

## Testing Strategy

### Unit Tests
```bash
cargo test -p simple-compiler error
cargo test -p simple-compiler i18n
```

### Manual Tests
```bash
# Test undefined variable with suggestion
echo 'print coun' > test.spl
./target/debug/simple test.spl

# Test channel closed error
./target/debug/simple simple/std_lib/test/features/errors/concurrency_errors_spec.spl
```

### I18n Test
```bash
LANG=ko ./target/debug/simple test.spl
```

---

## Success Criteria

- [ ] All 4 files compile without errors
- [ ] Error messages include error codes (E1001, E1013, etc.)
- [ ] Typo suggestions appear for undefined names
- [ ] Help text is contextual and actionable
- [ ] Korean translations load and display
- [ ] No test regressions
- [ ] Improved user experience for common errors

---

## Next Steps After Quick Wins

Once these quick wins are complete (estimated 2-3 hours):

1. **Expand to more error codes** (see main analysis report)
2. **Add SSpec test validation** for integrated codes
3. **Create error explanation examples** for docs
4. **Implement capability violation checks** (E1301-E1302)
5. **Integrate unique feature errors** (AOP, DI, etc.)

---

**Estimated Impact:**
- 20+ errors improved immediately
- Better developer experience for most common errors
- Foundation for remaining 100+ error code integrations
- Demonstrates error quality improvement to users

**Risk:** Low - Changes are additive and don't break existing functionality
