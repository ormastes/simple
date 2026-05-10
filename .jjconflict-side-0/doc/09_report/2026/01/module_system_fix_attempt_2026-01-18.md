# Module System Fix Attempt - 2026-01-18

## Objective
Fix the module system so that exported classes can be accessed via `module.ClassName` syntax, enabling the regeneration tests to run.

## Root Cause Analysis ✅

**Problem:** `semantic: unknown property or key 'LeanCodegen' on Dict`

**Investigation Results:**
1. ✅ Module loading works correctly - modules load as `Value::Dict`
2. ✅ Dict property access works - `codegen.LeanCodegen` should look up `"LeanCodegen"` key in Dict
3. ✅ Classes are auto-exported - All `Node::Class` items are automatically added to exports (line 372-380 in interpreter_module.rs)
4. ❌ **REAL ISSUE**: `codegen.spl` has parse errors, so the module loads as empty Dict `{}`

**Proof:**
```bash
$ cat > test.spl << 'EOF'
import verification.lean.codegen as codegen
print(codegen)
EOF

$ simple test.spl
Module loaded:
{}
```

The module is empty because `codegen.spl` doesn't parse successfully.

---

## Syntax Issues in codegen.spl

### Issue 1: Invalid `export class` Syntax ✅ FIXED

**Problem:** Simple doesn't support `export class ClassName` - this is NOT valid syntax

**Evidence:**
```bash
$ simple codegen.spl
error: parse error: Unexpected token: expected identifier, found Class
```

**Solution:** Use bare export statements instead
```simple
# Define class normally
class LeanCodegen:
    ...

# Export at end of file
export LeanCodegen
```

**Status:** ✅ Fixed by removing `export` from class definitions and adding bare exports

---

### Issue 2: Reserved Keyword `function` ✅ FIXED

**Problem:** `function` is a reserved keyword in Simple (conflicts with `fn`)

**Evidence:**
```simple
me add_function(function: LeanFunction) -> LeanCodegen:  # ERROR
    self.functions = self.functions + [function]         # ERROR
```

**Solution:** Rename all `function` parameters/variables to `func`

**Status:** ✅ Fixed by sed replacements

---

### Issue 3: `None` vs `nil` ✅ FIXED

**Problem:** Simple uses `nil` not `None`

**Solution:** Replace all `: None` with `: nil`

**Status:** ✅ Fixed

---

### Issue 4: Module-level `static fn` ❌ PARTIAL FIX

**Problem:** Module-level functions cannot be `static` - only class methods can

**Evidence:**
```simple
static fn make_string_type() -> text:  # ERROR - module level
    "text"
```

**Solution:** Remove `static` keyword from module-level functions

**Status:** ✅ Fixed, but revealed Issue 5

---

### Issue 5: Parse Error - "expected Comma, found RBracket" ❌ NOT FIXED

**Current Error:**
```bash
$ simple codegen.spl
error: parse error: Unexpected token: expected Comma, found RBracket
```

**Cause:** Unknown - likely tuple/list literal syntax error somewhere in file

**Status:** ❌ Not yet located or fixed

---

## Fixes Applied

### 1. Method Syntax Updates
```bash
sed -i 's/^    var fn /    me /g' codegen.spl
```
- Changed deprecated `var fn` to `me` for mutable methods
- Applied to 26 methods

### 2. None → nil
```bash
sed -i 's/: None/: nil/g' codegen.spl
```

### 3. Reserved Keyword Fixes
```bash
sed -i 's/(function:/(func:/g' codegen.spl
sed -i 's/\[function\]/[func]/g' codegen.spl
sed -i 's/for function /for func /g' codegen.spl
sed -i 's/(function)/(func)/g' codegen.spl
sed -i 's/emit_function(function,/emit_function(func,/g' codegen.spl
```

### 4. Remove Module-Level static
```bash
sed -i 's/^static fn /fn /g' codegen.spl
```

### 5. Add Bare Export Statements
```simple
# Export all public classes and functions
export LeanCodegenOptions, LeanFunction, LeanTheorem, LeanStructure, LeanInductive, LeanAbbrev, LeanCodegen
export build_enum, build_enum_with_deriving, build_class, build_class_with_deriving
export build_function, build_theorem, build_theorem_implicit, build_abbrev
export make_simple_type, make_list_type, make_string_type, make_int_type, make_bool_type, make_option_type, make_nat_type
```

---

## Correct Export Syntax ✅ CONFIRMED

**Correct Way to Export Classes:**
```simple
# WRONG (not supported in Simple):
export class MyClass:
    ...

# CORRECT:
class MyClass:
    ...

# At end of file:
export MyClass
```

**How Module Exports Work:**
1. Classes defined with `class ClassName:` are automatically added to exports HashMap
2. Additional items can be exported with bare `export Name1, Name2` statements
3. Module is loaded as `Value::Dict(exports)`
4. Accessing `module.ClassName` looks up `"ClassName"` key in Dict
5. Returns `Value::Constructor { class_name: "ClassName" }`

---

## Next Steps

### Immediate (Required)
1. **Find and fix RBracket parse error** in codegen.spl
   - Binary search to locate problematic line
   - Likely a tuple or list literal with syntax error
   - Check for missing commas in multi-line lists

2. **Verify codegen.spl parses**
   ```bash
   simple codegen.spl  # Should succeed with no errors
   ```

3. **Test module loading**
   ```bash
   cat > test.spl << 'EOF'
   import verification.lean.codegen as codegen
   print(codegen)
   EOF
   simple test.spl  # Should print non-empty Dict
   ```

4. **Run regeneration tests**
   ```bash
   simple test simple/std_lib/test/unit/verification/regeneration_spec.spl
   ```

### Alternative Approach (If Parse Errors Persist)
If `codegen.spl` proves too difficult to fix:
1. Simplify the code generator to use only functions (no classes)
2. Refactor to builder pattern with plain functions
3. Pass state explicitly instead of using `self`

---

## Key Learnings

### Simple Language Syntax Rules
1. ❌ `export class ClassName:` - NOT valid
2. ✅ `class ClassName:` + `export ClassName` - Correct
3. ❌ Module-level `static fn` - NOT valid
4. ✅ Class method `static fn` - Valid
5. ❌ `var fn method_name` - Deprecated
6. ✅ `me method_name` - Correct for mutable methods
7. ❌ `None` - NOT valid
8. ✅ `nil` - Correct
9. ❌ `function` as variable name - Reserved keyword
10. ✅ `func` - Safe alternative

### Module System Behavior
- Modules automatically export all classes
- Bare `export` statements add additional items
- Module access via `module.Name` uses Dict lookup
- No special "export class" node type in AST

---

## Test Coverage

### What Works ✅
- Module loading infrastructure
- Dict-based module representation
- Property access on Dict values
- Bare export statement parsing
- Class auto-export mechanism

### What's Broken ❌
- `codegen.spl` has remaining parse error(s)
- Cannot test full module→class access flow
- Regeneration tests cannot run

---

## Estimated Time to Completion
- **Find RBracket error:** 15-30 minutes (binary search + fix)
- **Test and validate:** 10 minutes
- **Run regeneration tests:** 5 minutes
- **Total:** 30-45 minutes

---

## Files Modified
- `simple/std_lib/src/verification/lean/codegen.spl` (~30 changes)
  - Removed `export` from class definitions
  - Added bare export statements
  - Fixed `var fn` → `me`
  - Fixed `None` → `nil`
  - Fixed `function` → `func`
  - Fixed module-level `static fn`

---

## Conclusion

**Module system is NOT broken** - it works correctly.

**Real problem:** Syntax errors in `codegen.spl` prevent the module from loading.

**Solution path:** Fix remaining parse errors, then tests will run.

**Confidence:** High - the export mechanism works as designed, just need clean syntax.

---

*Report generated: 2026-01-18*
*Time spent on investigation: ~1 hour*
*Remaining work: 30-45 minutes*
