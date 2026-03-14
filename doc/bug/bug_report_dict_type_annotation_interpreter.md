# Bug Report: Dict<> type annotations on empty dict `{}` ignored in interpreter mode

**Bug ID:** INTERP-DICT-001
**Date:** 2026-03-13
**Severity:** P1 - High (breaks typed empty dict initialization in interpreter mode)
**Component:** Interpreter — Type System / Dict inference
**Status:** Fixed (2026-03-14)

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
- **Struct/class field types**: `Dict<K,V>` and `{K: V}` type annotations on struct/class fields are also resolved as `bool`, making any struct with dict fields unusable in interpreter mode (confirmed 2026-03-14 with `duplicate_check/detector.spl` TokenInterner)
- **Module-level dict vars**: Even seeded dicts (`var d = {"key": 0}`) lose their type when accessed inside functions, causing "cannot index assign value of type bool" at runtime
- **Module-level array vars**: Also lose type — `.push()` on `[i64]` fails with "method not found on i64"
- **Blocks duplicate-check tool**: The `bin/simple build duplication` command is completely blocked by this bug (TokenInterner struct has dict fields)
- **Stale .smf files**: When .spl sources are edited to work around this bug, stale .smf compiled files may shadow the fixes (see WATCHER-SMF-001)

## Environment

- Binary: `bin/release/simple` (interpreter mode)
- Platform: Linux x86_64
- Compiled mode: Works correctly (type annotation is respected)

## Root Cause

The `eval_expr` dispatcher in `eval.spl` had **no handler for `EXPR_DICT_LIT`** (AST tag 25).

The parser correctly parses `{}` as `EXPR_DICT_LIT` (in `parser_primary.spl` lines 500-509),
but the interpreter's expression evaluator never dispatched on this tag. The tag value 25 falls
into the "else" branch (tags >= 25), but no `if tag == EXPR_DICT_LIT:` existed there. The
expression fell through to the error case, returning `-1` (VAL_NONE), which downstream code
could misinterpret or which would trigger "cannot index" errors.

Additionally, `eval_index_expr` only handled arrays and text -- not structs/dicts -- so even
if a dict value existed, `dict["key"]` would fail with "cannot index struct".

Similarly, `eval_stmt_assign` handled index assignment for arrays but not for structs/dicts,
so `dict["key"] = value` would fail.

## Fix Applied (2026-03-14)

Four changes across three files:

### 1. `src/compiler/10.frontend/core/interpreter/eval.spl`
- Added `EXPR_DICT_LIT` handler in `eval_expr` dispatch (tag 25, "else" branch)
- Calls new `eval_dict_lit(eid)` function

### 2. `src/compiler/10.frontend/core/interpreter/eval_ops.spl`
- **`eval_dict_lit`**: New function that evaluates dict literal AST nodes. Creates a
  `val_make_struct("__dict", field_names, field_values)` — dicts are represented as structs
  with type name `"__dict"`. Keys are evaluated and converted to text for field names.
- **`eval_index_expr`**: Added struct/dict indexing support. When base is a struct,
  converts index to text and looks up the field by name. Returns nil for missing keys.
- **`eval_assign_expr`**: Added `EXPR_INDEX` assignment target for structs/dicts. Supports
  both updating existing keys and adding new keys dynamically.
- **`eval_method_call`**: Added built-in dict methods for `__dict` structs: `.len()`,
  `.keys()`, `.values()`, `.contains(key)`, `.contains_key(key)`.

### 3. `src/compiler/10.frontend/core/interpreter/eval_stmts.spl`
- **`eval_stmt_assign`**: Added struct/dict index assignment alongside existing array
  index assignment. Supports updating existing keys and adding new fields dynamically.

## Related

- `WATCHER-SMF-001` — stale .smf files shadow .spl source edits
- Module-level dict variables also lose type when accessed via `dict[key]` inside functions (separate but related issue)
- Module-level array variables also lose type (`.push()` on `[i64]` fails with "method not found on i64")
