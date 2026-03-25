# Simple Language String System Summary

**Date:** 2025-12-29
**Context:** BDD Feature Documentation Implementation

## String Types in Simple (Per Spec)

### 1. Interpolated Strings - `"..."` or `f"..."`
**Default behavior with automatic interpolation:**
```simple
let name = "World"
let count = 42

# Both forms are identical (f-prefix is legacy/optional)
let msg1 = "Hello, {name}!"        # Recommended
let msg2 = f"Hello, {name}!"       # Also works (legacy)

# With expressions
let msg3 = "Result: {count + 10}"  # "Result: 52"

# Multi-line with \n escapes
let markdown = f"# {name}\n\n**Count:** {count}\n"
```

**Features:**
- ✅ Interpolation: `{expr}` embeds any expression
- ✅ Escape sequences: `\n`, `\t`, etc.
- ✅ Literal braces: `{{` and `}}` for `{` and `}`
- ✅ Works perfectly for all use cases

### 2. Raw Strings - `'...'`
**No interpolation, no escape processing:**
```simple
let regex = '[a-z]+\d{2,3}'      # \d is literal
let path = 'C:\Users\name'       # \U is literal
let template = '{name}'          # {name} is literal text
```

**Features:**
- ❌ NO interpolation: `{var}` is literal
- ❌ NO escape processing: `\n` is literal `\n`
- ✅ Perfect for: regex, file paths, templates

### 3. Doc Comments - `"""..."""`
**Documentation only, NOT string values:**
```simple
feature Calculator:
    """Core operations on a fresh calculator"""
    
    scenario Adding numbers:
        """Add two numbers together"""
        # ... test code
```

**Features:**
- ✅ Used for documentation in BDD framework
- ❌ NOT for multi-line string values
- ❌ NO interpolation support
- ❌ Cannot be assigned to variables

## What's NOT Supported (Yet)

### Triple-Quoted F-Strings - `f"""..."""`
**Requested but not implemented:**
```simple
# Desired syntax (doesn't work yet):
let markdown = f"""# {name}

**ID:** #{id}
**Category:** {category}
"""
# Error: Unterminated f-string

# Current workaround (works):
let markdown = f"# {name}\n\n**ID:** #{id}\n**Category:** {category}\n"
```

**Status:** Feature request filed in `improve_request.md`

## Best Practices

### For Simple Code (Current)

1. **Single-line interpolation:**
   ```simple
   let msg = f"Hello, {name}!"  # Clean and simple
   ```

2. **Multi-line templates:**
   ```simple
   # Use \n escapes
   let doc = f"# {title}\n\n{description}\n\n## Details\n{details}\n"
   ```

3. **Raw strings when you need literal text:**
   ```simple
   let regex = '[a-z]+'      # Use single quotes
   ```

### For Future (When f"""...""" is supported)

```simple
# This will be the cleanest way:
let markdown = f"""# {meta.name}

**Feature ID:** #{meta.id}
**Category:** {meta.category}
**Status:** {meta.status}

## Description

{meta.description}
"""
```

## Implementation Notes

### What We Learned
1. **Default interpolation** - `"..."` interpolates by default (no `f` needed)
2. **f-prefix is optional** - `f"..."` is same as `"..."` (legacy compatibility)
3. **Single quotes = raw** - `'...'` for literal strings
4. **Triple quotes = docs** - `"""..."""` for documentation, not values

### What Works in BDD Feature Doc
```simple
# ✅ This works perfectly:
let mut markdown = f"# {meta.name}\n\n"
markdown = markdown + f"**ID:** #{meta.id}\n"
markdown = markdown + f"**Category:** {meta.category}\n"

# ❌ This doesn't work (yet):
let markdown = f"""# {meta.name}

**ID:** #{meta.id}
**Category:** {meta.category}
"""
```

## Comparison with Other Languages

| Feature | Simple | Python | Rust |
|---------|--------|--------|------|
| Default interpolation | ✅ `"..."` | ❌ (needs `f""`) | ❌ (needs macro) |
| F-prefix | Optional | Required | N/A |
| Raw strings | `'...'` | `r"..."` | `r"..."` |
| Triple-quoted | Docs only | ✅ `"""..."""` | N/A |
| Triple f-strings | ❌ (requested) | ✅ `f"""..."""` | N/A |

## Summary

Simple's string system is **clean and intuitive**:
- Double quotes interpolate by default (unique feature!)
- Single quotes for raw strings
- F-prefix is optional (legacy)
- Triple-quoted f-strings requested but not yet implemented

**For now:** Use `f"...\n..."` with escape sequences for multi-line interpolated strings.

**Future:** When `f"""..."""` is implemented, upgrade to cleaner multi-line syntax.

---

**Related Documents:**
- `doc/spec/syntax.md` - String literals specification
- `simple/improve_request.md` - Feature request for `f"""..."""`
- `doc/report/BDD_FEATURE_DOC_COMPLETE_2025-12-29.md` - Implementation report
