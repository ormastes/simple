# Remaining Code Duplications - Analysis

**Date**: 2026-02-13  
**After**: 118 duplications eliminated

---

## Summary of Remaining Duplications

After eliminating 118 duplications, the following patterns remain in the codebase. This document categorizes them by feasibility of refactoring.

### Total Remaining: ~200+ duplicate blocks

---

## 1. Parser Binary Expression Handling (36 locations)

### Pattern:
```simple
match self.parse_X():
    case Ok(left):
        var current = left
        while self.check("operator"):
            self.advance()
            match self.parse_Y():
                case Ok(right):
                    current = Expr.Binary(op, current, right)
                case Err(e):
                    return Err(e)
        Ok(current)
    case Err(e):
        Err(e)
```

### Locations:
- `lib/pure/parser.spl` (12 instances)
- `lib/pure/parser_old.spl` (12 instances)
- `lib/parser/parser.spl` (12 instances)

### Why Not Refactored:
❌ **Requires higher-order functions** - Would need to pass:
- Left-hand parser function
- Operator check function
- Right-hand parser function
- Binary operator type

❌ **Runtime limitations** - Function parameters with closures don't work well

### Recommendation:
⏳ **Wait for runtime improvements** or accept as architectural duplication for clarity

### Potential Solution (if runtime allowed):
```simple
fn parse_binary_expr(
    left_parser: fn() -> Result<Expr>,
    op_check: fn() -> bool,
    right_parser: fn() -> Result<Expr>,
    make_op: fn() -> BinOp
) -> Result<Expr>:
    # Generic binary expression parser
```

---

## 2. Iterator Pattern (29 locations)

### Pattern:
```simple
var result = []
var continue = true

while continue:
    val next_result = iter_next_internal(iter)
    val elem = next_result[0]
    val has_more = next_result[1]
    
    if has_more:
        result.push(f(elem))  # or other operation
    else:
        continue = false

iter_from_array(result)
```

### Locations:
- `std/iterator/transform.spl` (10 instances)
- `std/iterator/filter.spl` (3 instances)
- `std/iterator/reduce.spl` (16 instances)

### Why Not Refactored:
❌ **Closure modification limitation** - Closures cannot modify outer `result` array

❌ **Different operations** - Each iteration does something different:
- `map`: `result.push(f(elem))`
- `filter`: `if predicate(elem): result.push(elem)`
- `fold`: `accumulator = f(accumulator, elem)`

### Recommendation:
⏳ **Wait for closure fix** - Requires runtime support for mutable closure captures

### Potential Solution (if runtime allowed):
```simple
fn iter_consume(iter, init, folder):
    """Generic iterator consumer with fold operation"""
    var result = init
    var continue = true
    while continue:
        val next_result = iter_next_internal(iter)
        val elem = next_result[0]
        val has_more = next_result[1]
        if has_more:
            result = folder(result, elem)
        else:
            continue = false
    result
```

---

## 3. Lazy Stream Pattern (20 locations)

### Pattern:
```simple
var continue = true

while continue:
    val next_result = stream_next_internal(stream)
    val elem = next_result[0]
    val has_next = next_result[1]
    
    if has_next:
        # operation on elem
    else:
        continue = false
```

### Locations:
- `std/lazy_utils.spl` (20 instances throughout file)

### Why Not Refactored:
❌ **Same as iterator pattern** - Closure modification limitation

### Recommendation:
✅ **Could be refactored similarly to iterators** once runtime is fixed

---

## 4. Test File Headers (22 locations)

### Pattern:
```simple
use compiler.parser.*
use compiler.parser_types.*
use compiler.lexer.*
use compiler.blocks.*
use compiler.treesitter.*
```

### Locations:
- `compiler/test_*.spl` (11 instances)
- `compiler_core_legacy/test_*.spl` (11 instances)

### Why Not Refactored:
✅ **Can be refactored easily!**

### Recommendation:
✅ **REFACTORABLE** - Create common test imports module

### Solution:
```simple
# test_common.spl
use compiler.parser.*
use compiler.parser_types.*
use compiler.lexer.*
use compiler.blocks.*
use compiler.treesitter.*

export parser, parser_types, lexer, blocks, treesitter

# test files:
use compiler.test_common.*
```

---

## 5. Git Compatibility Warnings (68 locations)

### Pattern:
```simple
val result = jj_run(cmd, repo_path)
if result.success:
    val warning = git_compat_warning("git_X", "jj Y", "jj_Z")
    make_tool_result(id, warning + result.stdout)
else:
    make_error_response(id, -32603, result.stderr)
```

### Locations:
- `src/app/mcp_jj/tools_git*.spl` (68 total)
  - `tools_git.spl` (34)
  - `tools_git_core.spl` (10)
  - `tools_git_branch.spl` (8)
  - `tools_git_sync.spl` (8)
  - `tools_git_misc.spl` (8)

### Why Not Refactored:
⚠️ **Intentional pattern** - Each git compatibility command needs:
- Specific warning message
- Command-specific output handling

✅ **Could create specialized helper** but pattern is clear and consistent

### Recommendation:
⏳ **Low priority** - Pattern is intentional and serves documentation purpose

### Potential Solution:
```simple
fn handle_git_compat_result(
    id: String, 
    result: JjResult,
    git_cmd: String,
    jj_equiv: String, 
    jj_tool: String
) -> String:
    if result.success:
        val warning = git_compat_warning(git_cmd, jj_equiv, jj_tool)
        make_tool_result(id, warning + result.stdout)
    else:
        make_error_response(id, -32603, result.stderr)
```

---

## 6. XML Child Iteration (13 locations)

### Pattern:
```simple
val children = xml_get_children(element)
var i = 0
val len = children.len()
while i < len:
    val child = children[i]
    # ... process child
    i = i + 1
```

### Locations:
- `std/xml_utils.spl` (various)
- `std/xml/dom.spl` (various)
- `std/xml/xpath.spl` (various)

### Why Not Refactored:
❌ **Closure limitation** - Cannot use callback pattern effectively

### Recommendation:
⏳ **Wait for closure fix** or accept as standard iteration pattern

---

## 7. Type System Phase Duplications (16+ locations)

### Pattern:
Entire files duplicated with slight variations:
- `compiler/trait_impl.spl` vs `compiler_core_legacy/trait_impl.spl`
- `compiler/trait_solver.spl` vs `compiler_core_legacy/trait_solver.spl`
- Multiple `associated_types_phase*.spl` files
- Multiple `higher_rank_poly_phase*.spl` files

### Why Not Refactored:
⚠️ **Architectural decision** - Appears to be intentional versioning for:
- Incremental compiler development
- Phase-by-phase implementation
- Regression testing different versions

### Recommendation:
🔍 **Needs investigation** - Determine if phase system is still needed:
- If yes: Document purpose and keep
- If no: Consolidate to single version

---

## Refactorability Matrix

| Duplication | Count | Feasible? | Priority | Blocker |
|-------------|-------|-----------|----------|---------|
| Parser binary expressions | 36 | ❌ No | Low | Higher-order functions |
| Iterator pattern | 29 | ❌ No | Medium | Closure modification |
| Lazy stream pattern | 20 | ❌ No | Medium | Closure modification |
| **Test file headers** | **22** | **✅ Yes** | **High** | **None!** |
| Git compat warnings | 68 | ⚠️ Maybe | Low | Intentional pattern |
| XML child iteration | 13 | ❌ No | Low | Closure limitation |
| Type phase files | 16+ | ⚠️ Maybe | Medium | Needs arch review |

---

## Actionable Recommendations

### Immediate (Can Do Now)

1. ✅ **Test File Headers** (22 duplications)
   - Create `test_common.spl` module
   - Replace 5-line headers with single import
   - **Effort**: 30 minutes
   - **Impact**: Cleaner test files

### Short Term (After Runtime Fixes)

2. ⏳ **Iterator Pattern** (29 duplications)
   - Wait for closure modification support
   - Create `iter_consume()` generic helper
   - **Effort**: 2 hours
   - **Impact**: Major stdlib improvement

3. ⏳ **Lazy Stream Pattern** (20 duplications)
   - Similar to iterator pattern
   - **Effort**: 1 hour
   - **Impact**: Cleaner lazy evaluation

### Medium Term (Requires Investigation)

4. 🔍 **Type Phase Files** (16+ duplications)
   - Review compiler phase architecture
   - Determine if versioning is still needed
   - Consolidate if obsolete
   - **Effort**: 4-8 hours
   - **Impact**: Major codebase simplification

5. ⚠️ **Git Compat Warnings** (68 duplications)
   - Optional: Create `handle_git_compat_result()` helper
   - **Effort**: 1 hour
   - **Impact**: Marginal (pattern is already clear)

### Long Term (Requires Language Changes)

6. ❌ **Parser Binary Expressions** (36 duplications)
   - Requires higher-order function improvements
   - Or accept as acceptable duplication for clarity
   - **Effort**: Language feature work
   - **Impact**: Cleaner parser implementation

7. ❌ **XML Child Iteration** (13 duplications)
   - Wait for closure improvements
   - **Effort**: Minimal once runtime fixed
   - **Impact**: Minor cleanup

---

## Summary

### Can Refactor Now:
- ✅ **Test headers** (22) - Easy win!

### Can Refactor After Runtime Fixes:
- ⏳ **Iterators** (29)
- ⏳ **Lazy streams** (20)
- ⏳ **XML iteration** (13)

### Needs Investigation:
- 🔍 **Type phase files** (16+)
- ⚠️ **Git warnings** (68) - optional

### Accept as Pattern:
- ❌ **Parser expressions** (36) - clarity over DRY
- ❌ **Some git warnings** - intentional pattern

---

## Next Steps

### Recommended Action Plan:

1. **Quick Win** (today): Refactor test file headers (22 duplications)
2. **Investigation** (this week): Review type phase file architecture
3. **Optional** (low priority): Consider git warning helper
4. **Wait** (future): Iterator/stream patterns after runtime improvements

### Total Potential Savings (if all fixed):
- **Immediate**: 22 duplications (test headers)
- **After runtime**: 62 duplications (iterators/streams)
- **After review**: 16+ duplications (phase files)
- **Total remaining**: ~100-120 duplications will likely remain as acceptable patterns

---

**Current Status**: 118 eliminated, ~200 remain  
**Next Target**: Test file headers (22 duplications, easy win!)
