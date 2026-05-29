# Enhanced Spec Features - Choose Your Options

**Date:** 2026-01-09

## Quick Summary

I propose adding these features to _spec.spl → markdown generation:

1. **Symbol Linking** - Link tests to implementation code
2. **Auto Symbol Detection** - Smart test name → symbol conversion
3. **Smart Path Resolution** - Use short names when clear
4. **Rich Markdown** - Symbol tables, TOC, cross-references

## Options - Please Choose

### 1. Symbol Linking Style

**A) Annotations (explicit)**
```simple
@links_to("Type::apply_subst")
test "my_test": ...
```

**B) Docstring metadata**
```simple
test "my_test":
    """
    **Links:** Type::apply_subst, Context::new
    """
```

**C) Auto-detect only**
```simple
# Parser finds symbols automatically
test "type_apply_subst": ...
```

**D) Hybrid (all methods) ⭐ RECOMMENDED**
- Docstring metadata when explicit needed
- Auto-detect from test names
- Scan code for symbol usage

**Your choice:** ___

### 2. Test Name Conversion

Convert `test_type_apply_subst` → find `type_apply_subst()` or `TypeApplySubst`?

- **Yes** ⭐ RECOMMENDED
- **No**

**Your choice:** ___

### 3. Path Resolution

**A) Smart (short when unambiguous)** ⭐
- `Type` when imported
- `simple_type::Type` when ambiguous

**B) Always full paths**
- `simple_type::types::Type` everywhere

**Your choice:** ___

### 4. Markdown Features (check all you want)

- [ ] Symbol index table
- [ ] Test-to-symbol links  
- [ ] Related tests section
- [ ] Source code links
- [ ] Quick TOC

**Your choices:** ___

## Example Output

**Input:**
```simple
test "type_inference_basic":
    """
    Test basic integer literal inference.
    **Links:** Type::infer_literal
    """
    let t = Type::infer_literal(42)
    assert t == Type::Int
```

**Generated Markdown:**
```markdown
### Test: type_inference_basic

**Linked Symbols:**
- [`Type::infer_literal`](../src/type/lib.rs#L156)

**Code:**
```simple
let t = Type::infer_literal(42)
assert t == Type::Int
```
```

## My Recommendations

✅ **Hybrid linking** (Option D)
✅ **Auto test name conversion** (Yes)  
✅ **Smart path resolution** (Option A)
✅ **All markdown features**

**Please confirm or adjust!**
