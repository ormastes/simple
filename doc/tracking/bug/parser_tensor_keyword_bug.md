# Parser Bug: "tensor" is a Reserved Keyword

**Date:** 2026-02-05
**Severity:** HIGH - Blocks Pure Simple Deep Learning
**Status:** ✅ WORKAROUND FOUND

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

## Recommendation for Compiler Team

1. **Document "tensor" as reserved keyword** in language specification
2. **Add compiler warning** when "tensor" is used as identifier
3. **OR Fix parser** to only enter tensor mode in appropriate contexts

---

**Resolution:** ✅ Workaround successful - all code fixed by renaming parameters
