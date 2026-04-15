# Parser Error Message Improvements

**Date:** 2026-01-17
**Purpose:** Improve error messages to help users debug parser issues

## Current Issue: Cryptic Error for `*const` Pointers

### Current Error
```
error: parse error: Unexpected token: expected identifier, found Const
```

**Problems:**
1. Doesn't indicate WHERE the error occurred (file, line, column)
2. Doesn't explain WHY it expected an identifier
3. Doesn't suggest a fix
4. Doesn't mention this is a known parser bug

### Improved Error (Proposed)

```
error: parse error at simple/std_lib/src/ui/gui/vulkan_ffi.spl:54:50
Unexpected token in pointer type

   54 | extern fn rt_vk_buffer_upload(buffer_handle: u64, data: *const u8, size: u64) -> i32
      |                                                          ^^^^^ unexpected keyword 'const'

Expected: type identifier after '*'
Found: keyword 'const'

Help: Pointer types with const/mut modifiers are not yet supported in Simple.
      This is a known parser bug.

      Workaround: Define wrapper types without raw pointers, or wait for fix.

      Tracking: Parser does not recognize '*const T' or '*mut T' pointer syntax.
                See: simple/bug_report_const_pointer_parsing.md
```

## Implementation Strategy

### 1. Add Contextual Error Messages

**Location:** `src/parser/src/parser_types.rs`

```rust
// After: TokenKind::Star =>
match &self.current.kind {
    TokenKind::Const => {
        return Err(self.error_with_help(
            format!("Unexpected keyword 'const' in pointer type"),
            "Pointer types with const/mut modifiers are not yet supported. \
             This is a known parser bug. \
             Workaround: Avoid using '*const T' or '*mut T' in FFI declarations."
        ));
    }
    TokenKind::Mut => {
        return Err(self.error_with_help(
            format!("Unexpected keyword 'mut' in pointer type"),
            "Pointer types with const/mut modifiers are not yet supported. \
             This is a known parser bug. \
             Workaround: Avoid using '*const T' or '*mut T' in FFI declarations."
        ));
    }
    _ => {}
}
```

### 2. Add Location Info to All Errors

**Current:** Most errors lack file/line/column info

**Needed:** Enhance error struct to always include:
- File path
- Line number
- Column number
- Snippet of code (5 lines context)
- Caret pointing to error location

**Example Format:**
```
error: <error-type> at <file>:<line>:<column>
<error-message>

   <line-num> | <source-code-line>
              | <caret-pointer>

<explanation>

<help-message-if-available>
```

### 3. Common Parser Errors to Improve

#### Error: Type Annotation in Val

**Current:**
```
error: parse error: Unexpected token: expected expression, found Colon
```

**Improved:**
```
error: parse error at test.spl:5:10
Type annotations not supported in 'val' declarations

    5 | val x: u64 = 42
      |       ^ type annotation not allowed here

Expected: val x = value
Found: val x: u64 = value

Help: Simple does not support type annotations in 'val' declarations.
      Use type suffixes instead:

      val x = 42_u64  # Use suffix for typed literal

      Or use type inference:

      val x = 42  # Type inferred as Int
```

#### Error: Missing Use Statement

**Current:**
```
error: compile failed: parse: Unexpected token: expected identifier, found Const
```

When trying to import vulkan_ffi.spl

**Improved:**
```
error: failed to parse module 'ui.gui.vulkan_ffi'
Parse error in simple/std_lib/src/ui/gui/vulkan_ffi.spl:54:50

   54 | extern fn rt_vk_buffer_upload(buffer_handle: u64, data: *const u8, size: u64) -> i32
      |                                                          ^^^^^

Module cannot be imported due to syntax error.

Cause: Pointer type '*const T' is not yet supported by the parser.

Help: This module is currently unusable. Avoid importing it with 'use' statements.
      Track progress: simple/bug_report_const_pointer_parsing.md
```

### 4. Error Categories

Classify errors by category for better diagnostics:

```rust
pub enum ParseErrorKind {
    UnexpectedToken {
        expected: Vec<String>,
        found: String,
        context: String,  // "in pointer type", "in val declaration", etc.
    },
    UnsupportedFeature {
        feature: String,
        workaround: Option<String>,
        tracking_issue: Option<String>,
    },
    InvalidSyntax {
        explanation: String,
        suggestion: Option<String>,
    },
}
```

### 5. Logging Improvements

**Add Debug Logging for Parser State:**

```rust
// In parser_types.rs, add tracing
#[instrument(skip(self), level = "debug")]
fn parse_single_type(&mut self) -> Result<Type, ParseError> {
    debug!("Parsing type, current token: {:?}", self.current.kind);

    match &self.current.kind {
        TokenKind::Star => {
            debug!("Found Star token, checking for const/mut");
            self.advance();
            debug!("Next token after Star: {:?}", self.current.kind);

            // Error with context
            if matches!(self.current.kind, TokenKind::Const | TokenKind::Mut) {
                error!(
                    "Parser bug: *const/*mut not implemented. \
                     File: {:?}, Line: {}, Token: {:?}",
                    self.filename,
                    self.current.span.line,
                    self.current.kind
                );
            }

            let inner = self.parse_single_type()?;
            // ...
        }
        // ...
    }
}
```

**Output Format:**
```
DEBUG parse_single_type: Parsing type, current token: Star
DEBUG parse_single_type: Found Star token, checking for const/mut
DEBUG parse_single_type: Next token after Star: Const
ERROR parse_single_type: Parser bug: *const/*mut not implemented. \
                          File: "simple/std_lib/src/ui/gui/vulkan_ffi.spl", \
                          Line: 54, Token: Const
```

## Testing Error Messages

Create SSpec tests for error messages:

```simple
# simple/std_lib/test/features/parser/error_messages_spec.spl

describe "Parser error messages":
    context("Const pointer bug"):
        it "provides helpful error for *const pointer":
            # Test that error message includes:
            # - File and line number
            # - Snippet of code
            # - Explanation of issue
            # - Workaround suggestion
            pass

    context("Val type annotation"):
        it "provides helpful error for val with type annotation":
            # Test error message quality
            pass
```

## Priority

**P1 - High Priority**

Better error messages reduce user frustration and support burden. Implement alongside parser bug fixes.

## Implementation Checklist

- [ ] Add `ParseErrorKind` enum with categories
- [ ] Enhance error struct with file/line/column info
- [ ] Add code snippet rendering (5-line context with caret)
- [ ] Add contextual help messages for common errors
- [ ] Improve logging with tracing spans
- [ ] Add debug logging for parser state at key decision points
- [ ] Create SSpec tests for error message quality
- [ ] Document error message conventions

## References

- Parser implementation: `src/parser/src/parser_types.rs`
- Error handling: `src/parser/src/error.rs`
- Logging: Use `tracing` crate
- Related bug: `simple/bug_report_const_pointer_parsing.md`
