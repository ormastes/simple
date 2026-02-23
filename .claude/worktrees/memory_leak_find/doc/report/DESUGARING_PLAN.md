# Full Simple → Core Simple Desugaring Plan

**Date:** 2026-02-10  
**Status:** Research & Planning  
**Goal:** Make Full Simple code compilable by Core Simple (seed compiler)

---

## Executive Summary

**Problem:** Full Simple (src/compiler/, 52K lines) uses advanced language features that Core Simple (src/compiler_core_legacy/, 8.8K lines) cannot parse or compile.

**Solution:** Desugar Full Simple → Core Simple compatible code via systematic transformations.

**Target:** Enable `seed.cpp` → compile Core → compile desugared Full → bootstrap complete

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│ SEED (C++ Bootstrap Runtime)                                    │
│ - bootstrap/seed.cpp (~143K lines)                              │
│ - Provides runtime for initial bootstrap                        │
│ - Can compile Core Simple only                                  │
└────────────────┬────────────────────────────────────────────────┘
                 │ compiles
                 ▼
┌─────────────────────────────────────────────────────────────────┐
│ CORE SIMPLE (Seed-Compilable Subset)                            │
│ - src/compiler_core_legacy/ (~8.8K lines)                                       │
│ - RESTRICTIONS (no syntactic sugar):                            │
│   ❌ No impl blocks                                             │
│   ❌ No generics (<T>)                                          │
│   ❌ No closures/lambdas                                        │
│   ❌ No traits with dynamic dispatch                            │
│   ❌ No exception handling (try/catch)                          │
│   ❌ No multi-line boolean expressions                          │
│   ❌ No Option<T>, Result<T,E> types                           │
│   ✅ Only: i64, f64, text, bool, [i64], [text], structs        │
│   ✅ Integer tags for enums (no payloads)                       │
│   ✅ Module-level vars + functions                              │
│   ✅ Simple if/while/for control flow                           │
└────────────────┬────────────────────────────────────────────────┘
                 │ should compile (after desugaring)
                 ▼
┌─────────────────────────────────────────────────────────────────┐
│ FULL SIMPLE (Complete Language Implementation)                  │
│ - src/compiler/ (~52K lines)                                    │
│ - CURRENT FEATURES (that break Core):                           │
│   ✅ impl blocks with methods                                   │
│   ✅ Generics: Option<T>, HashMap<K,V>                         │
│   ✅ Closures: |x| x + 1                                        │
│   ✅ Traits with dynamic dispatch                               │
│   ✅ Pattern matching with enum payloads                        │
│   ✅ Advanced operators: ?., ??, .?                            │
│   ✅ Tree-sitter integration                                    │
│   ✅ Type inference (Hindley-Milner)                           │
└─────────────────────────────────────────────────────────────────┘
```

---

## Feature Analysis: Full vs Core

### ❌ Feature 1: `impl` Blocks

**Full Simple:**
```simple
struct Parser:
    source: text
    pos: i64

impl Parser:
    static fn new(source: text) -> Parser:
        Parser(source: source, pos: 0)
    
    me advance():
        self.pos = self.pos + 1
    
    me current_char() -> text:
        self.source[self.pos:self.pos + 1]
```

**Core Simple (Module-level functions):**
```simple
struct Parser:
    source: text
    pos: i64

fn parser_new(source: text) -> Parser:
    Parser(source: source, pos: 0)

fn parser_advance(self: Parser) -> Parser:
    Parser(source: self.source, pos: self.pos + 1)

fn parser_current_char(self: Parser) -> text:
    self.source[self.pos:self.pos + 1]
```

**Transformation:**
- `impl Type:` → Remove block, convert methods to functions
- `static fn name(...)` → `fn type_name(...)`
- `me method(...)` → `fn type_method(self: Type, ...)`
- Method calls: `obj.method(args)` → `type_method(obj, args)`

---

### ❌ Feature 2: Generics

**Full Simple:**
```simple
struct Option<T>:
    is_some: bool
    value: T

fn wrap<T>(val: T) -> Option<T>:
    Option(is_some: true, value: val)
```

**Core Simple (Monomorphization for common types):**
```simple
struct OptionI64:
    is_some: bool
    value: i64

struct OptionText:
    is_some: bool
    value: text

fn wrap_i64(val: i64) -> OptionI64:
    OptionI64(is_some: true, value: val)

fn wrap_text(val: text) -> OptionText:
    OptionText(is_some: true, value: val)
```

**OR use tagged unions:**
```simple
# Generic-like container using integer tags
var opt_tag: i64 = 1  # 0=None, 1=Some
var opt_i64: i64 = 42
var opt_text: text = "hello"
```

**Transformation:**
- Monomorphize for concrete instantiations: `Option<i64>` → `OptionI64`
- OR erase to tagged unions with `any` type (runtime checked)

---

### ❌ Feature 3: Closures

**Full Simple:**
```simple
fn filter(list: [i64], predicate: fn(i64) -> bool) -> [i64]:
    var result: [i64] = []
    for x in list:
        if predicate(x):
            result = result.push(x)
    result

val nums = [1, 2, 3, 4, 5]
val evens = filter(nums, |x| x % 2 == 0)
```

**Core Simple (Lambda lifting):**
```simple
fn filter(list: [i64], predicate_fn: i64) -> [i64]:
    # predicate_fn is a function pointer index
    var result: [i64] = []
    var i: i64 = 0
    while i < list.len():
        val x: i64 = list[i]
        if call_predicate(predicate_fn, x):
            result = result.push(x)
        i = i + 1
    result

fn is_even(x: i64) -> bool:
    x % 2 == 0

val nums: [i64] = [1, 2, 3, 4, 5]
val evens: [i64] = filter(nums, 0)  # 0 = function index for is_even
```

**Transformation:**
- Lift closures to top-level functions
- Pass function index or pointer instead of closure
- Capture variables → Pass as extra parameters

---

### ❌ Feature 4: Option Type with `?` Operators

**Full Simple:**
```simple
struct Node:
    value: i64
    next: Node?

fn get_next_value(node: Node) -> i64:
    node.next?.value ?? 0
```

**Core Simple:**
```simple
struct Node:
    value: i64
    has_next: bool
    next_value: i64
    next_has_next: bool
    # ... flatten recursively

fn get_next_value(node: Node) -> i64:
    if node.has_next:
        node.next_value
    else:
        0
```

**OR use sentinel values:**
```simple
fn get_next_value(node: Node, next_valid: bool, next_val: i64) -> i64:
    if next_valid:
        next_val
    else:
        0
```

---

### ❌ Feature 5: Pattern Matching

**Full Simple:**
```simple
enum Result:
    Ok(i64)
    Error(text)

fn handle(res: Result) -> i64:
    match res:
        Ok(val): val
        Error(msg): 
            print("Error: " + msg)
            -1
```

**Core Simple:**
```simple
struct Result:
    tag: i64        # 0=Ok, 1=Error
    ok_value: i64
    error_msg: text

fn handle(res: Result) -> i64:
    if res.tag == 0:
        res.ok_value
    else:
        print("Error: " + res.error_msg)
        -1
```

**Transformation:**
- Enum with payloads → Struct with tag + union fields
- `match` → `if-else` chain checking tags

---

### ❌ Feature 6: Tree-sitter Integration

**Full Simple:**
```simple
use treesitter.*

fn parse_outline(source: text) -> Outline:
    val ts = TreeSitter.new(source)
    ts.parse_outline()
```

**Core Simple (Direct token parsing):**
```simple
use core.lexer.*
use core.parser.*

fn parse_outline(source: text) -> Outline:
    lex_init(source)
    parse_module()
```

**Transformation:**
- Remove tree-sitter dependency
- Use direct token-based parsing from `core.parser`

---

## Transformation Strategy

### Phase 1: Manual Prototype (1-2 files)

Pick a small, representative file from Full Simple and manually convert it:

**Target file:** `src/compiler/lexer.spl` (simplest with clear transformations)

**Steps:**
1. Remove `impl Lexer:` block
2. Convert `static fn new()` → `fn lexer_new()`
3. Convert `me next()` → `fn lexer_next(self: Lexer)`
4. Remove `Option<T>` → Use tag + nullable fields
5. Replace `.?` operator → Explicit `if` checks
6. Document all transformations

**Output:** `src/compiler/lexer_desugared.spl` (Core-compatible)

---

### Phase 2: Automated Desugarer Tool

Write a compiler pass that transforms Full → Core:

**Tool structure:**
```simple
# scripts/tools/desugarer/main.spl
fn desugar_file(input_path: text, output_path: text):
    val full_ast = parse_full_simple(input_path)
    val core_ast = transform_to_core(full_ast)
    write_core_simple(core_ast, output_path)

fn transform_to_core(ast: Module) -> Module:
    var core_module = Module(...)
    
    # Pass 1: Remove impl blocks → Convert to functions
    for impl_block in ast.impls:
        core_module = desugar_impl_block(core_module, impl_block)
    
    # Pass 2: Monomorphize generics
    core_module = monomorphize_generics(core_module)
    
    # Pass 3: Lift closures
    core_module = lift_closures(core_module)
    
    # Pass 4: Desugar pattern matching
    core_module = desugar_match(core_module)
    
    # Pass 5: Replace advanced operators
    core_module = desugar_operators(core_module)
    
    core_module
```

**Transformations:**

1. **Impl Block Removal:**
   - Input: `impl Type: { ... methods ... }`
   - Output: `fn type_method(self: Type, ...) { ... }`

2. **Generic Monomorphization:**
   - Collect all generic instantiations: `Option<i64>`, `Option<text>`
   - Generate concrete types: `struct OptionI64 { ... }`
   - Replace usage sites

3. **Closure Lifting:**
   - Detect closures: `|params| body`
   - Extract to top-level: `fn closure_N(params) { body }`
   - Replace with function reference

4. **Option/Result Desugaring:**
   - `Option<T>` → Struct with `is_some: bool, value: T`
   - `Result<T,E>` → Struct with `is_ok: bool, ok_val: T, err_val: E`

5. **Operator Desugaring:**
   - `obj?.method()` → `if obj_valid: obj.method() else: nil`
   - `a ?? b` → `if a_valid: a else: b`

---

### Phase 3: Integration & Testing

**Build pipeline:**
```bash
# Step 1: Desugar Full Simple
simple-desugarer src/compiler/*.spl --output src/compiler_core_legacy/

# Step 2: Compile with seed
seed_compiler src/compiler_core_legacy/*.spl --output build/compiler.cpp

# Step 3: Compile C++ → Binary
g++ build/compiler.cpp -o bin/simple-compiler

# Step 4: Verify bootstrap
bin/simple-compiler src/compiler/*.spl
```

**Verification:**
1. ✅ All desugared files compile with seed
2. ✅ Generated binaries produce correct output
3. ✅ Full test suite passes (604+ tests)
4. ✅ Bootstrap cycle completes: Simple compiles itself

---

## Implementation Roadmap

### Week 1: Manual Prototype
- [ ] Convert `lexer.spl` to Core-compatible form
- [ ] Convert `parser.spl` to Core-compatible form
- [ ] Document all transformations needed
- [ ] Verify Core compiler can build them

### Week 2: Desugarer Core
- [ ] Implement AST traversal framework
- [ ] Implement impl block removal
- [ ] Implement basic monomorphization
- [ ] Implement closure lifting

### Week 3: Advanced Features
- [ ] Implement pattern match desugaring
- [ ] Implement Option/Result desugaring
- [ ] Implement operator desugaring
- [ ] Handle tree-sitter removal

### Week 4: Integration & Testing
- [ ] Integrate desugarer into build system
- [ ] Run full test suite
- [ ] Fix compatibility issues
- [ ] Optimize performance

### Week 5: Bootstrap Verification
- [ ] Complete bootstrap cycle
- [ ] Performance benchmarking
- [ ] Documentation updates
- [ ] Release candidate

---

## Success Criteria

✅ **Functional:**
- [ ] All Full Simple files desugar without errors
- [ ] Desugared code compiles with seed compiler
- [ ] Generated binaries are functionally equivalent
- [ ] Full test suite passes (604+ tests)

✅ **Performance:**
- [ ] Desugaring completes in <5 seconds
- [ ] Binary size within 20% of hand-written
- [ ] Runtime performance within 10% of original

✅ **Maintainability:**
- [ ] Clear mapping: Full feature → Core equivalent
- [ ] Automated with minimal manual intervention
- [ ] Good error messages for unsupported features
- [ ] Documentation for each transformation

---

## Current Status

**Files analyzed:**
- ✅ Core Simple constraints documented
- ✅ Full Simple features cataloged
- ✅ Architecture understood
- 🔄 Manual prototype: NOT STARTED
- 🔄 Automated desugarer: NOT STARTED

**Next Steps:**
1. Choose target file for manual prototype (`lexer.spl` recommended)
2. Manually convert to Core-compatible form
3. Test compilation with seed
4. Document transformation patterns
5. Begin desugarer implementation

---

## References

- **Architecture:** `doc/design/core_full_unified_architecture.md`
- **Core Simple:** `src/compiler_core_legacy/` (8.8K lines)
- **Full Simple:** `src/compiler/` (52K lines)
- **Seed Bootstrap:** `bootstrap/seed.cpp` (143K lines)

---

## Questions for Research

1. **Generic Strategy:** Monomorphization vs type erasure?
   - Monomorphization: Generates code for each instantiation (bloat)
   - Type erasure: Single implementation with runtime checks (slower)

2. **Closure Captures:** How to handle captures?
   - Option A: Pass captured vars as extra parameters
   - Option B: Create closure struct with captured fields

3. **Tree-sitter Removal:** How critical is it?
   - Can we keep it as optional feature?
   - Or must we fully remove dependency?

4. **Error Messages:** How to preserve good diagnostics?
   - Desugarer must map errors back to original source locations

5. **Incremental Compilation:** How to handle?
   - Desugar only changed files?
   - Or full rebuild each time?

---

**End of Document**
