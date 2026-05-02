# Parser Bug: "tensor" is a Reserved Keyword

**Date:** 2026-02-05
**Severity:** HIGH - Blocks Pure Simple Deep Learning
**Status:** ✅ FIXED (2026-04-03)

---

## Summary

The Simple parser treats **"tensor" as a special/reserved keyword** that triggers tensor expression parsing mode. Using "tensor" as a parameter or variable name causes parse errors.

**Error Message:**
```
error: parse error: Unexpected token: expected identifier for tensor name, found Dot
```

---

## Root Cause

When the parser sees a variable named "tensor" followed by a dot (`.`), it enters a special parsing mode for tensor operations (like dotted operators `.+`, `.-`, etc.) instead of treating it as a normal field access.

---

## Minimal Reproduction

```simple
class PureTensor<T>:
    shape: [i64]

# ❌ FAILS - "tensor" triggers special parsing
fn get_shape<T>(tensor: PureTensor<T>) -> [i64]:
    tensor.shape  # Parse error here

# ✅ WORKS - Any other name works fine
fn get_shape<T>(t: PureTensor<T>) -> [i64]:
    t.shape  # Works perfectly
```

---

## Workaround

**Never use "tensor" as a variable/parameter name.** Use alternatives:
- `t`, `x`, `arr`, `data`, `input`, `output`, etc.

---

## Fix Applied

Automated rename across entire Pure Simple DL codebase:
- `tensor:` → `t:` (parameters)
- `tensor.` → `t.` (field access)
- `(tensor` → `(t` (expressions)
- 29 files processed

---

## Fix (2026-04-03)

**Root cause:** The lexer unconditionally emitted `TokenKind::Tensor` for the word "tensor",
making it a hard keyword that could never be used as an identifier without special-case
handling in every parser context.

**Fix:** Removed "tensor" from the keyword table in the Rust bootstrap lexer
(`src/compiler_rust/parser/src/lexer/identifiers.rs`). "tensor" is now lexed as a
regular `TokenKind::Identifier`. Tensor literal syntax (`tensor K: Float [d=2, h=3]`)
is detected contextually in the parser: when the identifier "tensor" is immediately
followed by another identifier token (the tensor name), the parser enters tensor
literal parsing mode.

**Files changed:**
- `src/compiler_rust/parser/src/lexer/identifiers.rs` -- emit regular identifier instead of keyword
- `src/compiler_rust/parser/src/expressions/primary/mod.rs` -- contextual tensor literal detection
- `src/compiler_rust/parser/src/expressions/primary/math.rs` -- add `parse_tensor_literal_from_ident`, fix `check_ident` for keyword sub-tokens (slice/flat/default)
- `src/compiler_rust/parser/src/expressions/primary/identifiers.rs` -- remove `TokenKind::Tensor` handler
- `src/compiler_rust/parser/src/parser_helpers.rs` -- remove `TokenKind::Tensor` from helper functions
- `src/compiler_rust/parser/src/parser_patterns.rs` -- remove `TokenKind::Tensor` pattern handler

**Resolution:** ✅ Fixed -- "tensor" is now a regular identifier; tensor literal syntax preserved via contextual parsing
