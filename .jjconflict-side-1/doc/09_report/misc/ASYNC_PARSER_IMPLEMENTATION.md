# Async/Await Parser Implementation

**Date:** 2026-02-11
**Status:** ✅ Parser Support Complete

## Summary

Successfully implemented parser support for async/await syntax in the Simple language compiler. The parser can now recognize and parse `async fn`, `await`, `yield`, and `spawn` expressions.

## Implementation Details

### 1. AST Changes (src/compiler_core/ast.spl)

**Added async function support:**
- Added `var decl_is_async: [i64] = []` to track async functions
- Modified `decl_alloc()` to initialize `decl_is_async.push(0)`
- Modified `decl_fn()` signature to accept `is_async: i64` parameter
  ```simple
  fn decl_fn(name: text, param_names: [text], param_types: [i64],
             ret_type: i64, body: [i64], is_async: i64, span_id: i64) -> i64
  ```

**Added async expression constructors:**
```simple
fn expr_await(future_expr: i64, span_id: i64) -> i64:
    val idx = expr_alloc(EXPR_AWAIT, span_id)
    expr_left[idx] = future_expr
    idx

fn expr_yield(value_expr: i64, span_id: i64) -> i64:
    val idx = expr_alloc(EXPR_YIELD, span_id)
    expr_left[idx] = value_expr
    idx

fn expr_spawn(call_expr: i64, span_id: i64) -> i64:
    val idx = expr_alloc(EXPR_SPAWN, span_id)
    expr_left[idx] = call_expr
    idx
```

### 2. Parser Changes (src/compiler_core/parser.spl)

**Imported async tokens:**
```simple
use core.tokens.{TOK_KW_ASYNC, TOK_KW_AWAIT, TOK_KW_YIELD, TOK_KW_SPAWN}
use core.ast.{EXPR_AWAIT, EXPR_YIELD, EXPR_SPAWN}
use core.ast.{expr_await, expr_yield, expr_spawn}
```

**Modified parse_fn_decl() to accept is_async:**
```simple
fn parse_fn_decl(is_async: i64) -> i64:
    # ... existing parameter parsing ...
    decl_fn(fn_name, param_names, param_types, ret_type, body, is_async, 0)
```

**Modified parse_module_body() to detect async fn:**
```simple
elif par_kind == TOK_KW_ASYNC:
    # Async function: async fn name()
    parser_advance()
    if par_kind == TOK_KW_FN:
        val d = parse_fn_decl(1)  # 1 = is_async
        module_add_decl(d)
    else:
        parser_error("expected 'fn' after 'async'")
elif par_kind == TOK_KW_FN:
    val d = parse_fn_decl(0)  # 0 = not async
    module_add_decl(d)
```

**Added expression parsing in parse_primary():**
```simple
if par_kind == TOK_KW_AWAIT:
    parser_advance()
    val future_expr = parse_expr()
    return expr_await(future_expr, 0)

if par_kind == TOK_KW_YIELD:
    parser_advance()
    val value_expr = parse_expr()
    return expr_yield(value_expr, 0)

if par_kind == TOK_KW_SPAWN:
    parser_advance()
    val call_expr = parse_expr()
    return expr_spawn(call_expr, 0)
```

## Testing

**Test file:** `/tmp/test_async_parser.spl`

```simple
# Async function declaration
async fn fetch_data() -> i64:
    42

# Await expression
fn test_await():
    val result = await fetch_data()
    print result

# Yield expression
fn generator() -> i64:
    yield 1
    yield 2
    yield 3
    0

# Spawn expression
fn test_spawn():
    val task = spawn fetch_data()
    print "Spawned task"
```

**Result:** ✅ Parsed successfully without errors

## Additional Fixes

Fixed blocking build error in `src/lib/src/dl/config_loader.spl`:
- Removed module-level variable `_config_state` (runtime limitation)
- Changed `Result<DLConfig, text>` → `DLConfig?` (no generics at runtime)
- Disabled user config caching to work around module closure bug

## What's Next

The parser and basic interpreter integration are complete. To fully enable async/await functionality, the following steps remain:

1. ✅ **Interpreter Integration** - Basic stubs added to prevent crashes
   - Added `eval_await_expr()`, `eval_yield_expr()`, `eval_spawn_expr()`
   - Currently evaluate synchronously (no state machine support)
   - Note: Full async runtime (`src/lib/async/`) exists but uses generics (runtime limitation)

2. ⏳ **Desugar Pipeline Integration** - Connect two AST systems
   - Core parser uses `core.ast` (arena-based, what I modified)
   - Desugar pipeline uses `compiler.parser_types` (struct-based)
   - Need conversion layer or unified AST
   - Pipeline ready: `suspension_analysis.spl`, `state_enum.spl`, `poll_generator.spl`

3. ⏳ **Runtime Async Support** - State machine execution
   - Current: async functions return Promise objects but await fails
   - Need: State machine execution in interpreter OR
   - Alternative: Compile async functions to native code

4. ⏳ **Test Enablement** - Un-skip 70+ async tests
   - Many tests skip_it(reason: "async/await not implemented")
   - Can enable once full state machine support works

## Files Modified

- `src/compiler_core/ast.spl` - Added async support to declarations and expressions
- `src/compiler_core/parser.spl` - Added async parsing logic
- `src/lib/src/dl/config_loader.spl` - Fixed module-level variable issues

## Files Created

- `/tmp/test_async_parser.spl` - Parser validation test

---

*Parser implementation complete - interpreter integration required for full functionality*
