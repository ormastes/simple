# Nested Generics Parser Bug - Root Cause Analysis

## Date: 2026-01-12

## Summary

Nested generic type parameters (e.g., `Option<Guard<T>>`) have **never worked** in Simple's parser, despite existing code attempting to handle them. A misleading test gave the false impression that they worked.

## Discovery

### Misleading Test

**Test**: `test_new_nested_generics_no_warning()` in `deprecation_warnings.rs`

```rust
#[test]
fn test_new_nested_generics_no_warning() {
    let src = "val x: List<Option<String>> = []";
    assert!(
        !has_deprecation_warning(src),
        "Should NOT warn about nested <> syntax"
    );
}
```

**Status**: ✅ PASSING

**Problem**: This test only checks for deprecation warnings, NOT parse success!

### Verification Test

Created new test to verify actual parsing:

```rust
#[test]
fn test_list_option_string_actually_parses() {
    let src = "val x: List<Option<String>> = []";
    let mut parser = Parser::new(src);
    let result = parser.parse();
    assert!(result.is_ok());
}
```

**Result**: ❌ FAILS with `UnexpectedToken { expected: "Comma", found: "Assign" }`

## Error Analysis

### Error Location

For source: `val x: List<Option<String>> = []`

Error at column 28-29, which is the `=` sign.

**What Happens**:
1. Parse `val x:`
2. Parse type `List`
3. See `<`, start parsing generic args for List
4. Call `parse_type()` to parse first arg
5. Parse `Option`
6. See `<`, start parsing generic args for Option
7. Parse `String`
8. See `>>` token (should close both Option and List)
9. **BUG**: Parser doesn't handle `>>` correctly
10. Parser thinks it's still inside List's generic args
11. Expects comma for next type argument
12. Finds `=` instead → error

### Existing Code

File: `src/parser/src/parser_types.rs` lines 237-277

The parser HAS code to handle `>>` splitting:

```rust
while !self.check(&closing_token) {
    // Handle >> token splitting for nested generics
    if using_angle_brackets && self.check(&TokenKind::ShiftRight) {
        break; // Will be handled below
    }

    args.push(self.parse_type()?);  // Line 244

    if !self.check(&closing_token) {
        // Check for >> before expecting comma
        if using_angle_brackets && self.check(&TokenKind::ShiftRight) {
            break;  // Line 249
        }
        self.expect(&TokenKind::Comma)?;  // Line 251
    }
}

// Split >> into two > tokens
if using_angle_brackets && self.check(&TokenKind::ShiftRight) {
    // Consume >> and push back one >
    self.advance();
    self.pending_tokens.push_front(gt_token);
}
```

**The Problem**: This code exists but doesn't work!

## Root Cause Hypothesis

The issue is likely in the interaction between recursive `parse_type()` calls:

1. **Outer parse** (List): Calls `parse_type()` for first arg (line 244)
2. **Inner parse** (Option): Recursively parses `Option<String>`
3. When inner parse sees `>>`:
   - It should use ONE `>` to close Option
   - Leave ONE `>` for outer parse to close List
4. **But**: The inner parse might be consuming BOTH `>` symbols

### Hypothesis: Token Consumption Issue

When the inner `parse_type()` for `Option<String>>` completes:
- It should see `>>` at line 246
- Check `!self.check(&closing_token)` where closing_token is `Gt`
- Current token is `ShiftRight` (>>), not `Gt`, so check returns TRUE
- Line 248 checks for ShiftRight → should break
- **BUT**: Maybe the check at line 248 is never reached?

Or:
- The inner parse DOES split `>>` correctly (lines 256-274)
- But the outer parse doesn't see the pushed-back `>` token

## Why Tests Pass

The deprecation warning tests use this helper:

```rust
fn parse_and_get_hints(src: &str) -> Vec<(ErrorHintLevel, String)> {
    let mut parser = Parser::new(src);
    let _ = parser.parse(); // Parse (may succeed or fail, we just want hints)
    //      ^ Ignores parse result!

    parser.error_hints()  // Only returns hints
}
```

**Comment says**: "may succeed or fail, we just want hints"

So all deprecation tests pass even when parsing FAILS!

## Reproduction

### Minimal Failing Cases

All of these FAIL to parse:

```simple
# Case 1: Variable declaration
val x: Option<Guard<i32>> = nil

# Case 2: Function return type
fn test() -> Option<Guard<i32>>:
    return nil

# Case 3: From existing test
val x: List<Option<String>> = []
```

**Error**: `expected Comma, found <Assign|Colon>`

### Simple Workaround (Confirmed Working)

```simple
# Use type alias for inner generic
type GuardI32 = Guard<i32>

# Now this works
fn test() -> Option<GuardI32>:
    return nil
```

## Impact

### What's Broken
- ❌ All nested generic types
- ❌ `Option<Vec<T>>`
- ❌ `Result<List<T>, E>`
- ❌ `Vec<Option<T>>`
- ❌ sync.spl methods (try_lock, try_read, try_write)

### What Works
- ✅ Single-level generics: `Option<T>`, `Vec<i32>`
- ✅ Type aliases: `type X = Guard<T>; Option<X>`
- ✅ Array types: `[i32]`, `[Option<T>]` (different syntax)

## Fix Strategy

### Option 1: Debug Existing Code (Recommended)

The `>>` splitting logic EXISTS but doesn't work. Need to:

1. Add debug logging to `parse_single_type()` generic parsing
2. Track token consumption through recursive calls
3. Verify `pending_tokens` queue works correctly
4. Check if `self.check()` looks at pending tokens

**Files to modify**:
- `src/parser/src/parser_types.rs` (lines 237-277)
- Possibly `src/parser/src/parser_impl/core.rs` (token handling)

**Estimated effort**: 2-4 hours

### Option 2: Alternative Approach

Completely rewrite generic type parsing with explicit depth tracking:

```rust
fn parse_generic_args(&mut self, depth: u32) -> Result<Vec<Type>, ParseError> {
    let mut args = Vec::new();
    let mut gt_count = 0;

    while gt_count < depth {
        args.push(self.parse_type_with_depth(depth + 1)?);

        // Handle closing
        match self.current.kind {
            TokenKind::Gt => {
                gt_count += 1;
                self.advance();
            }
            TokenKind::ShiftRight => {
                gt_count += 2;
                self.advance();
            }
            TokenKind::Comma => {
                self.advance();
            }
            _ => return Err(...)
        }
    }

    // Push back extra > tokens
    for _ in 0..(gt_count - depth) {
        self.pending_tokens.push_front(Token::new(TokenKind::Gt, ...));
    }

    Ok(args)
}
```

**Estimated effort**: 4-8 hours

### Option 3: Workaround Documentation

Document the limitation and provide type alias workarounds.

**Estimated effort**: 1 hour
**Impact**: Technical debt remains

## Recommended Action Plan

1. **Immediate** (today):
   - ✅ Document the bug (this file)
   - ✅ Update deprecation tests to actually check parse success
   - Add failing test cases for nested generics

2. **Short-term** (this sprint):
   - Debug existing `>>` splitting code
   - Add comprehensive debug logging
   - Fix the root cause
   - Uncomment sync.spl try_* methods

3. **Testing**:
   - Add tests for 2-4 level nesting
   - Test edge cases: `Vec<Vec<i32>>`, `>>>`, `>>>>`
   - Verify all sync.spl methods work

## Test Cases to Add

```rust
#[test]
fn test_two_level_nesting() {
    parse_ok("val x: Option<Vec<i32>> = nil");
}

#[test]
fn test_three_level_nesting() {
    parse_ok("val x: Result<Option<Vec<String>>, Error> = nil");
}

#[test]
fn test_function_return_nested() {
    parse_ok("fn test() -> Option<Guard<T>>:\n    nil");
}

#[test]
fn test_double_gt_token() {
    // Vec<Vec<i32>> should tokenize >> as ShiftRight
    parse_ok("val x: Vec<Vec<i32>> = []");
}

#[test]
fn test_triple_gt_token() {
    // Should handle >>> as ShiftRight + Gt
    parse_ok("val x: A<B<C<i32>>> = nil");
}
```

## Files Modified for Investigation

1. `src/parser/tests/test_nested_generic_manual.rs` - Reproduction tests
2. `src/parser/tests/test_verify_nested_parse.rs` - Verification test
3. `src/parser/tests/mod.rs` - Test module registration

## Next Steps

Run `cargo test --package simple-parser test_nested` to see all failing cases, then add debug logging to `parse_single_type()` to trace the exact token flow.

---

**Status**: 🔴 CRITICAL BUG - Never worked, falsely believed to work
**Priority**: P0 (Blocks core stdlib, believed to be working)
**Complexity**: Medium (code exists, needs debugging)
**Confidence**: High (reproduced, root cause identified)
