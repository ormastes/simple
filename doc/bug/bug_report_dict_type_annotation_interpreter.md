# Bug Report: Dict<> type annotations on empty dict `{}` ignored in interpreter mode

**Bug ID:** INTERP-DICT-001
**Date:** 2026-03-13
**Severity:** P1 - High (breaks typed empty dict initialization in interpreter mode)
**Component:** Interpreter — Type System / Dict inference
**Status:** Confirmed, workaround available

## Summary

Dict type annotations on empty dict literals `{}` are ignored by the interpreter. The empty dict is inferred as `bool` instead of the annotated dict type, causing runtime errors when the dict is later accessed with index syntax.

Both annotation styles are affected:
1. `Dict<text, i64>` generic syntax
2. `{text: i64}` shorthand syntax

This works correctly in compiled mode — the bug is interpreter-only.

## Minimal Reproduction

```simple
# Bug: explicit Dict type annotation ignored, empty dict inferred as bool
var breakpoints: Dict<text, i64> = {}
breakpoints["main"] = 42
# CRASH: "cannot index value of type bool"

# Same bug with shorthand syntax
var counts: {text: i64} = {}
counts["hello"] = 1
# CRASH: "cannot index value of type bool"
```

## Observed Behavior

| Declaration | Expected Type | Actual Type (Interpreter) |
|------------|---------------|---------------------------|
| `var d: Dict<text, i64> = {}` | `Dict<text, i64>` | `bool` |
| `var d: {text: i64} = {}` | `{text: i64}` | `bool` |
| `var d = {"key": 0}` | `Dict<text, i64>` | `Dict<text, i64>` (correct) |

The interpreter appears to evaluate `{}` as a standalone expression (which resolves to a falsy/bool value) rather than respecting the type annotation to construct a typed empty dict.

## What Works (Workarounds)

### Seed with a dummy entry

```simple
var breakpoints = {"__init__": 0}
breakpoints["main"] = 42   # works
```

Initialize the dict with a throwaway key-value pair so the interpreter can infer the correct type from the literal content rather than the annotation.

### Use array-based storage instead

```simple
var bp_keys = [""]
var bp_count = 0

fn has_bp(key: text) -> bool:
    var i = 0
    for k in bp_keys:
        if i < bp_count and k == key:
            return true
        i = i + 1
    false
```

## Impact

- **DAP test files**: Multiple test files under `test/feature/dap/` require typed empty dicts for breakpoint tracking, variable watches, and session state
- **Any interpreter-mode code** that needs an initially-empty dict with a known key/value type
- Forces use of dummy-seeded dicts or array-based workarounds, which obscure intent

## Environment

- Binary: `bin/release/simple` (interpreter mode)
- Platform: Linux x86_64
- Compiled mode: Works correctly (type annotation is respected)

## Related

- Module-level dict variables also lose type when accessed via `dict[key]` inside functions (separate but related issue)
- The interpreter evaluates `{}` as a block/expression rather than as a dict literal when no entries are present
