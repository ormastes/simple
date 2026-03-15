# Bug Report: Dict.get() Auto-Unwraps Optional in Interpreter

**Bug ID:** INTERP-DICT-002
**Date:** 2026-03-15
**Severity:** P2 (workaround available, type safety concern)
**Component:** Interpreter
**Status:** Confirmed

## Summary

`Dict<text, text>.get(key)` returns a raw `str` value instead of `text?` (optional) in the interpreter when the key exists. Calling `.unwrap()` on the result fails with `method 'unwrap' not found on type 'str'` because the value is already unwrapped.

## Minimal Reproduction

```simple
use compiler.common.config.{Config}

var config = Config.default()
config.set("key1", "value1")

# FAILS:
val result = config.get("key1")    # should be text?, actually returns str
expect(result.unwrap()).to_equal("value1")
# Error: semantic: method `unwrap` not found on type `str` (receiver value: value1)

# WORKS (direct comparison):
val result = config.get("key1")
expect(result).to_equal("value1")

# ALSO WORKS (.? check):
val result = config.get("key1")
expect(result.?).to_equal(true)    # .? still works correctly
```

## Root Cause Analysis

The interpreter's `Dict.get()` implementation returns the value directly when the key is found, rather than wrapping it in `Some(value)`. The `.?` operator still works (likely through a separate code path that checks for nil/non-nil), but `.unwrap()` fails because the value is already a raw `str`, not an `Optional<text>`.

This creates an inconsistency: `.?` returns `true` (treating it as present optional), but `.unwrap()` fails (treating it as non-optional).

**Relevant source:** `Config.get()` at `src/compiler/00.common/config.spl:55-56` delegates to `Dict.get()` which is implemented in the runtime.

## Observed Behavior

| Expression | Expected | Actual |
|------------|----------|--------|
| `config.get("key1")` | `Some("value1")` (text?) | `"value1"` (str) |
| `config.get("key1").?` | `true` | `true` (works) |
| `config.get("key1").unwrap()` | `"value1"` | Error: method 'unwrap' not found on type 'str' |
| `config.get("missing")` | `nil` | `nil` (works) |
| `config.get("missing").?` | `false` | `false` (works) |

## Impact

- Cannot use idiomatic `val v = dict.get(key).unwrap()` pattern
- Type safety gap: code cannot distinguish between "key exists with value" and raw value
- Affects all `Dict.get()` calls where the return value needs `.unwrap()`

## Workaround

Compare the result directly without `.unwrap()`:

```simple
val result = config.get("key")
expect(result).to_equal("expected_value")
```

Or use `.?` to check presence, then compare directly:

```simple
val result = config.get("key")
if result.?:
    expect(result).to_equal("expected_value")
```

## Environment

- Simple compiler: interpreter mode
- Discovered in: `test/unit/compiler/config/compiler_config_spec.spl`
