# seed_cpp Translation Capabilities & Limitations

## Overview

`seed/seed.cpp` is a C++ transpiler for Simple language, designed for bootstrapping. It translates `.spl` → `.cpp` with runtime library calls.

**Status:** Minimal bootstrap (simple main functions) ✅ | Full compiler bootstrap ⚠️

## What seed_cpp CAN Handle

### ✅ Basic Features
- **Functions:** `fn name(args) -> type:` with body
- **Main function:** `fn main() -> i32:` (generates `spl_main`)
- **Print statements:** `print "text"` → `spl_println("text")`
- **Integer literals:** `0`, `42`, `-1`
- **String literals:** `"hello"`, with escapes
- **Variable declarations:** `val x = y`, `var x = y`
- **Function calls:** `name()`, `name(arg1, arg2)`
- **Return statements:** `return expr`, implicit return
- **Structs:** Basic struct definitions (no methods)
- **Simple type annotations:** `i64`, `i32`, `f64`, `text`, `bool`

### ✅ Control Flow
- **If statements:** `if cond:` / `elif:` / `else:`
- **While loops:** `while cond:`
- **For loops:** `for x in range(n):` (numeric expressions treated as range)
- **Match statements:** Simple enum matching (no data extraction)
- **Break/continue:** Basic loop control

### ✅ Operators
- **Arithmetic:** `+`, `-`, `*`, `/`, `%`
- **Comparison:** `==`, `!=`, `<`, `>`, `<=`, `>=`
- **Logical:** `and`, `or`, `not`
- **String concat:** `"text" + expr` → `spl_str_concat()`

### ✅ Arrays
- **Struct arrays:** `[StructType]` → `std::vector<StructType>`
- **Array literals:** `[1, 2, 3]` → `spl_array_new()` + pushes
- **Array indexing:** `arr[i]`

### ✅ Type Inference
- **Struct field access:** `obj.field` → infers field type
- **Function return types:** Tracks and uses for further inference
- **For-loop variables:** Infers element type from array type

## What seed_cpp CANNOT Handle

### ❌ Advanced Type System
- **Generics:** `Option<T>`, `List<Int>` → causes "incomplete type" errors
- **Generic functions:** `fn foo<T>(x: T):` → not recognized
- **Trait bounds:** `where T: Trait` → ignored/fails
- **Associated types:** `type Item = T` → translation errors

### ❌ Pattern Matching
- **Enum data extraction:** `case Some(x):` → "undeclared identifier"
- **Complex patterns:** `case Point(x, y):` → not translated
- **Pattern destructuring:** `val (a, b) = tuple` → fails

### ❌ Operators & Syntax
- **Optional chaining:** `.?` → parse/translation error
- **Null coalescing:** `??` → not recognized
- **Pipe operator:** `|>` → not handled
- **Lambda syntax:** `\x: x + 1` → not recognized
- **Comprehensions:** `[for x in items: x * 2]` → fails

### ❌ Classes & Methods
- **Class definitions:** `class Name:` with methods → partial support
- **Method calls:** `obj.method()` → may treat as field access
- **Self parameter:** `self` in methods → may not bind correctly
- **Mutable self:** `me method():` → not recognized
- **Static methods:** `static fn` → not handled
- **Constructors:** `Type(field: val)` → creates wrong code

### ❌ Advanced Features
- **Closures:** Function parameters with `fn() -> T` type → wrong translation
- **Higher-order functions:** Passing functions as values → fails
- **Async/await:** Not supported
- **Actors:** Not supported
- **Macros:** Not supported
- **Attributes:** `@annotation` → ignored

### ❌ Module System
- **Use statements:** `use module.{name}` → parsed but not linked
- **Export:** `export name` → parsed but not enforced
- **Module paths:** Not resolved during translation

## Translation Quality Issues

### ⚠️ Struct Initialization
**Problem:** Missing `return` statements
```cpp
// Generated code (WRONG):
SomeStruct somestruct_new() {
    SomeStruct{.field = value};  // Missing return!
}
```

**Workaround:** Manually add returns or fix seed_cpp generator

### ⚠️ Function Stubs
**Problem:** `output_has_problems()` heuristic is conservative
```cpp
// When translation uncertain:
int32_t some_func() {
    return 0; /* stub */
}
```

**Trigger:** Complex expressions, unknown types, parsing ambiguity

### ⚠️ Type Coercion
**Problem:** Int/string conversions not automatic
```cpp
// Generated (WRONG):
const char* x = some_int_value;  // Type mismatch!
```

## Recommendations

### For Minimal Bootstrap
Use seed_cpp for simple driver code:
```simple
fn bootstrap_hello():
    print "Simple Bootstrap Compiler v0.1"

fn main() -> i32:
    bootstrap_hello()
    0
```
✅ This works perfectly after Bug #1 and Bug #2 fixes!

### For Extended Bootstrap
**Option A:** Stub complex modules
- Create simplified versions of trait/generic/async code
- Use `/* stub */` implementations for non-critical features
- Focus on core lexer/parser/codegen only

**Option B:** Improve seed_cpp
- Add generic type support
- Implement pattern matching translation
- Handle `.?` operator
- Fix struct initialization bugs

**Option C:** Hybrid approach
- Use seed_cpp for 50-100 simple files
- Hand-write C++ for complex modules
- Link together for bootstrap compiler

### For Full Self-Hosting
Don't use seed_cpp - use native Simple compiler once available.

## Test Coverage

| Feature | Test File | Status |
|---------|-----------|--------|
| Main function | bootstrap_main.spl | ✅ Works |
| Simple functions | (embedded in all files) | ✅ Works |
| Struct arrays | (embedded) | ✅ Works |
| Generic types | Option<T>, List<T> | ❌ Fails |
| Pattern matching | trait tests | ❌ Fails |
| Classes with methods | aop.spl | ⚠️  Partial |

## Future Work

1. **Immediate:** Use seed_cpp only for minimal bootstrap (10-20 files)
2. **Short-term:** Hand-craft C++ for complex compiler modules
3. **Long-term:** Replace seed_cpp with native Simple→native compiler

## Related Files

- `seed/seed.cpp` - Main transpiler (C++)
- `seed/runtime.c/h` - Runtime library
- `scripts/bootstrap-fixed.sh` - Bootstrap script using seed_cpp
- `doc/report/seed_cpp_main_fix_2026-02-13.md` - Bug fix report
