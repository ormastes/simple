# Making Full Simple Compilable by Core Simple

**Goal:** Enable Core Simple (seed-compilable) to compile Full Simple (compiler implementation)

**Status:** ✅ Research Complete | 🔄 Implementation Not Started

**Date:** 2026-02-10

---

## Quick Summary

The Simple language has a **three-tier bootstrap architecture**:

```
SEED (C++)  →  CORE SIMPLE  →  FULL SIMPLE
 143K lines     8.8K lines      52K lines
  (Runtime)    (Restricted)    (Full Lang)
```

**Problem:** Full Simple uses advanced features (generics, closures, impl blocks, pattern matching) that Core Simple cannot parse.

**Solution:** Desugar Full Simple code into Core-compatible form via mechanical transformations.

---

## Key Restrictions

### Core Simple CAN'T use:
- ❌ `impl` blocks with methods
- ❌ Generics: `<T>`, `Option<T>`, `HashMap<K,V>`
- ❌ Closures: `|x| x + 1`
- ❌ Traits with dynamic dispatch
- ❌ Pattern matching with enum payloads
- ❌ Advanced operators: `?.`, `??`, `.?`
- ❌ Multi-line boolean expressions
- ❌ Exception handling

### Core Simple CAN use:
- ✅ Module-level functions
- ✅ Concrete types: `i64`, `f64`, `text`, `bool`
- ✅ Arrays: `[i64]`, `[text]`
- ✅ Structs with named fields
- ✅ Enums with integer tags (no payloads)
- ✅ Simple control flow: `if`, `while`, `for`
- ✅ `var`/`val` bindings

---

## Transformation Examples

### 1. Impl Blocks → Module Functions

**Before:**
```simple
impl Parser:
    static fn new(source: text) -> Parser: ...
    me parse() -> Module: ...
```

**After:**
```simple
fn parser_new(source: text) -> Parser: ...
fn parser_parse(self: Parser) -> Module: ...
```

### 2. Option Types → Tagged Fields

**Before:**
```simple
struct Lexer:
    pending: Token?
```

**After:**
```simple
struct Lexer:
    has_pending: bool
    pending_value: Token
```

### 3. Pattern Matching → If-Else

**Before:**
```simple
match token.kind:
    case IntLit | FloatLit: true
    case _: false
```

**After:**
```simple
val is_int: bool = token.kind == TOK_INT_LIT
val is_float: bool = token.kind == TOK_FLOAT_LIT
val result: bool = is_int or is_float
```

### 4. Closures → Lifted Functions

**Before:**
```simple
list.filter(|x| x > 10)
```

**After:**
```simple
fn is_greater_than_10(x: i64) -> bool: x > 10
list_filter(list, is_greater_than_10)
```

---

## Implementation Plan

### Phase 1: Manual Prototype (Week 1)
**Goal:** Prove the concept with one file

- [ ] Pick target file: `src/compiler/lexer.spl` (1,430 lines)
- [ ] Manually convert to Core-compatible form
- [ ] Document all transformations needed
- [ ] Test compilation with seed
- [ ] Verify functional equivalence

**Output:** `src/compiler_core/lexer.spl` (Core-compatible)

---

### Phase 2: Automated Desugarer (Weeks 2-3)
**Goal:** Tool that mechanically transforms Full → Core

**Tool Structure:**
```simple
# src/tools/desugarer/main.spl
fn desugar_file(input: text, output: text):
    val ast = parse_full_simple(input)
    val core_ast = transform_ast(ast)
    write_core_simple(core_ast, output)

fn transform_ast(ast: Module) -> Module:
    ast
        .remove_impl_blocks()
        .monomorphize_generics()
        .lift_closures()
        .desugar_pattern_match()
        .desugar_option_types()
        .replace_operators()
```

**Transformations to Implement:**

1. **Impl Block Removal** (Easy)
   - Input: `impl Type: { fn method() }`
   - Output: `fn type_method(self: Type)`
   - Rename pattern: `Type.method` → `type_method`

2. **Generic Monomorphization** (Medium)
   - Collect instantiations: `Option<i64>`, `Option<text>`
   - Generate concrete types: `OptionI64`, `OptionText`
   - Replace call sites

3. **Closure Lifting** (Medium)
   - Detect: `|params| body`
   - Extract: `fn closure_N(params) { body }`
   - Handle captures (pass as parameters)

4. **Pattern Match Desugaring** (Medium)
   - `match expr: case pat: val` → if-else chains
   - Tuple patterns → separate comparisons
   - `|` (or) → logical OR

5. **Option Type Desugaring** (Easy)
   - `Option<T>` → `has_value: bool, value: T`
   - `Some(x)` → `has_value = true, value = x`
   - `nil` → `has_value = false`
   - `.?` → check `has_value`
   - `.unwrap()` → access `value`

6. **Operator Replacement** (Easy)
   - `a?.b` → `if a_valid: a.b else: default`
   - `a ?? b` → `if a_valid: a else: b`

---

### Phase 3: Integration & Testing (Week 4)
**Goal:** Integrate desugarer into build pipeline

**Build Pipeline:**
```bash
# Step 1: Desugar Full → Core
simple-desugarer src/compiler/*.spl --output src/compiler_core/

# Step 2: Compile with seed
seed_compiler src/compiler_core/*.spl --output build/compiler.cpp

# Step 3: Build C++ binary
g++ build/compiler.cpp -o bin/simple-compiler

# Step 4: Bootstrap test
bin/simple-compiler src/compiler/*.spl --output bin/simple-final
```

**Verification:**
- [ ] All 52K lines desugar without errors
- [ ] Desugared code compiles with seed
- [ ] Generated binaries work correctly
- [ ] Full test suite passes (604+ tests)
- [ ] Bootstrap cycle completes

---

### Phase 4: Optimization & Polish (Week 5)
**Goal:** Production-ready desugarer

- [ ] Performance: Desugar in <5 seconds
- [ ] Error messages: Map back to original source locations
- [ ] Documentation: Each transformation explained
- [ ] CI integration: Auto-desugar on build
- [ ] Release notes

---

## Success Criteria

### Functional ✅
- [ ] All Full Simple files desugar without errors
- [ ] Desugared code compiles with Core/seed
- [ ] Binaries are functionally equivalent
- [ ] 604+ tests pass

### Performance ✅
- [ ] Desugaring time: <5 seconds
- [ ] Binary size: within 20% of original
- [ ] Runtime performance: within 10% of original

### Maintainability ✅
- [ ] Clear transformation documentation
- [ ] Good error messages
- [ ] Automated with minimal manual intervention
- [ ] Easy to extend for new features

---

## File Statistics

### Core Simple (src/core/):
```
Total: 8,823 lines
- lexer_struct.spl: 719 lines
- parser.spl: 1,188 lines
- ast.spl + ast_types.spl: 940 lines
- types.spl: 367 lines
```

### Full Simple (src/compiler/):
```
Total: 52,414 lines
- parser.spl: 2,357 lines
- lexer.spl: 1,430 lines
- 100+ other files
- Uses: impl, generics, closures, pattern matching
```

### Seed Bootstrap (bootstrap/):
```
- seed.cpp: 143,691 lines
- seed.c: 83,828 lines
- Can only compile Core Simple
```

---

## Quick Start: Manual Prototype

**Recommended first file:** `src/compiler/lexer.spl` (1,430 lines)

**Why this file?**
- Small enough to convert manually (1-2 days)
- Clear transformations (impl → functions, Option → tags)
- No complex dependencies
- Easy to test in isolation

**Steps:**
```bash
# 1. Copy file
cp src/compiler/lexer.spl src/compiler_core/lexer.spl

# 2. Edit src/compiler_core/lexer.spl
# - Remove impl Lexer: block
# - Convert methods to functions
# - Desugar Option types
# - Replace pattern matching

# 3. Test compilation
seed_cpp src/compiler_core/lexer.spl --output build/lexer.cpp

# 4. Test functionality
simple test test/unit/compiler/lexer_spec.spl
```

---

## References

- **Main Plan:** [DESUGARING_PLAN.md](DESUGARING_PLAN.md)
- **Detailed Example:** [LEXER_DESUGARING_EXAMPLE.md](LEXER_DESUGARING_EXAMPLE.md)
- **Architecture:** [doc/design/core_full_unified_architecture.md](doc/design/core_full_unified_architecture.md)

---

## Current Status

**Research:**
- ✅ Core constraints documented
- ✅ Full features analyzed
- ✅ Transformation patterns identified
- ✅ Example file chosen (lexer.spl)

**Implementation:**
- 🔄 Manual prototype: NOT STARTED
- 🔄 Automated desugarer: NOT STARTED
- 🔄 Integration testing: NOT STARTED
- 🔄 Bootstrap verification: NOT STARTED

---

## Next Actions

### Immediate (This Week):
1. **Manual prototype:** Convert `src/compiler/lexer.spl` to Core form
2. **Test compilation:** Verify seed can compile it
3. **Document learnings:** Note any unexpected challenges

### Short Term (Next 2 Weeks):
4. **Build desugarer:** Implement transformation tool
5. **Test on lexer:** Verify automated tool produces same output
6. **Expand coverage:** Apply to 5-10 more files

### Medium Term (Month 1):
7. **Full coverage:** All 52K lines desugared
8. **Integration:** Add to build pipeline
9. **Testing:** Full test suite passes
10. **Bootstrap:** Complete self-hosting cycle

---

## Questions & Decisions

### 1. Generic Strategy
**Options:**
- A) Monomorphization (generate code for each type)
- B) Type erasure (single implementation, runtime checks)

**Recommendation:** Start with monomorphization for common types (Option, Result), use erasure for rare cases.

### 2. Closure Captures
**Options:**
- A) Pass as extra parameters
- B) Create closure struct with fields

**Recommendation:** Option A (simpler, no new types).

### 3. Tree-sitter Dependency
**Options:**
- A) Remove entirely (use token parsing)
- B) Keep as WFFI library

**Recommendation:** Option B (less invasive, tree-sitter is valuable).

### 4. Error Messages
**Challenge:** How to preserve good diagnostics after desugaring?

**Solution:** Maintain source maps: desugared line → original line.

---

## Timeline

- **Week 1:** Manual prototype complete
- **Week 2-3:** Automated desugarer working
- **Week 4:** Integration and testing
- **Week 5:** Polish and release

**Total Estimated Effort:** 3-4 person-weeks

---

**End of Plan**
