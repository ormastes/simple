# Extern Function Call Flow Analysis

## Current (Broken) Flow

```
User Code:
  extern fn rt_file_exists(path: text) -> i64
  val x = rt_file_exists("/tmp/test")
                 |
                 v
eval.spl:eval_call()
                 |
                 v
         [Check builtin_call?]
              NO (rt_file_exists is not print/int/etc)
                 |
                 v
         [Check func_table_lookup?]
              NO (extern fn not registered!)
                 |
                 v
         [Check env_lookup?]
              NO (not a variable)
                 |
                 v
         ERROR: "undefined function: rt_file_exists"
```

## After Fix Flow

```
User Code:
  extern fn rt_file_exists(path: text) -> i64
  val x = rt_file_exists("/tmp/test")
                 |
                 v
eval.spl:eval_call()
                 |
                 v
         [Check builtin_call?]
              NO
                 |
                 v
         [Check func_table_lookup?]
              YES! (decl_id = X)
                 |
                 v
eval_function_call(decl_id, args)
                 |
                 v
         [Get decl node]
         [Check if body_stmts empty?]
              YES (extern fn has no body)
                 |
                 v
         [Call C runtime rt_file_exists()]
                 |
                 v
         Return value to user
```

## Registration Comparison

### Regular Function (WORKS)

```simple
fn my_function(x: i64) -> i64:
    x * 2
```

**eval.spl:1766-1768**
```simple
if tag == DECL_FN:
    func_table_register(d_node.name, did)  ← Registered!
    func_register_return_type(d_node.name, d_node.ret_type)
```

**Result:** Function callable via `my_function(5)`

### Extern Function (BROKEN)

```simple
extern fn rt_file_exists(path: text) -> i64
```

**eval.spl:1769-1770**
```simple
if tag == DECL_EXTERN_FN:
    # func_table_register() NOT CALLED!
    func_register_return_type(d_node.name, d_node.ret_type)
```

**Result:** Function NOT callable - "undefined function" error

## The Missing Line

**Only ONE line is missing:**

```diff
 if tag == DECL_EXTERN_FN:
+    func_table_register(d_node.name, did)
     func_register_return_type(d_node.name, d_node.ret_type)
```

This single line unlocks **ALL** extern function support.

## Function Table Structure

The function table is a simple name → decl_id map:

```
Function Table (Dict):
┌─────────────────────┬────────────┐
│ Function Name       │ Decl ID    │
├─────────────────────┼────────────┤
│ "my_function"       │ 42         │ ← Regular function
│ "another_function"  │ 43         │ ← Regular function
│ "rt_file_exists"    │ MISSING!   │ ← Extern (BUG!)
└─────────────────────┴────────────┘
```

After fix:
```
Function Table (Dict):
┌─────────────────────┬────────────┐
│ Function Name       │ Decl ID    │
├─────────────────────┼────────────┤
│ "my_function"       │ 42         │
│ "another_function"  │ 43         │
│ "rt_file_exists"    │ 44         │ ← NOW REGISTERED!
└─────────────────────┴────────────┘
```

## Decl Node Structure

Both regular and extern functions have decl nodes:

**Regular Function Decl:**
```
CoreDecl {
    tag: DECL_FN (1)
    name: "my_function"
    param_names: ["x"]
    param_types: [TYPE_I64]
    ret_type: TYPE_I64
    body_stmts: [stmt_id_1, stmt_id_2, ...]  ← HAS BODY
}
```

**Extern Function Decl:**
```
CoreDecl {
    tag: DECL_EXTERN_FN (2)
    name: "rt_file_exists"
    param_names: ["path"]
    param_types: [TYPE_TEXT]
    ret_type: TYPE_I64
    body_stmts: []  ← NO BODY (empty array)
}
```

The interpreter checks `body_stmts.len() == 0` to dispatch to C runtime.

## Why This Bug Went Unnoticed

1. **Bootstrapping:** Seed compiler uses C++ directly, not the interpreter
2. **Limited extern usage:** Most Simple code uses wrapper functions, not raw externs
3. **Built-in functions:** Common operations (print, int) are in `eval_builtin_call()`
4. **Import workarounds:** People use `use` imports instead of `extern` declarations

## What This Unlocks

Once fixed:

- ✅ All 33+ rt_ functions (file I/O, processes, time, JIT)
- ✅ FFI libraries (CUDA, Torch, compression, crypto, regex, SQLite)
- ✅ Package management (uses extern functions)
- ✅ External integrations (MCP servers, databases)
- ✅ System programming (mmap, file locks, process spawn)

## Verification Steps

After applying fix:

1. **Unit test:** Direct extern call
2. **Integration test:** Stdlib using extern
3. **Regression test:** Full test suite (4067 tests)
4. **Performance test:** No slowdown expected (just registration)
