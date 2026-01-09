# Enhanced Spec Features Implementation Plan

**Status:** Implementing
**Date:** 2026-01-09
**Approach:** Recommended options (Hybrid, Auto-convert, Smart paths, All features)

---

## Implementation Overview

### Phase 1: Core Features ✅ Planned
1. Symbol linking (hybrid approach)
2. Test name to symbol conversion
3. Smart path resolution
4. Enhanced markdown generation

### Phase 2: Root TOC Generation ✅ Planned
1. Category detection
2. Cross-spec navigation
3. Hierarchical TOC

---

## Phase 1: Enhanced Spec Features

### 1.1 Symbol Linking (Hybrid)

**Methods:**
- **Docstring metadata:** `**Links:** Symbol::method`
- **Auto-detect from test name:** `test_type_inference` → `type_inference()`, `TypeInference`
- **Code scanning:** Parse function calls and type usage

**Implementation:**
```python
def extract_symbols_hybrid(test_case):
    symbols = []
    
    # Method 1: Explicit docstring
    if "**Links:**" in test_case.docstring:
        explicit = parse_links_metadata(test_case.docstring)
        symbols.extend(explicit)
    
    # Method 2: Test name conversion
    name_symbols = convert_test_name_to_symbols(test_case.name)
    symbols.extend(name_symbols)
    
    # Method 3: Code scanning
    code_symbols = scan_code_for_symbols(test_case.code)
    symbols.extend(code_symbols)
    
    return deduplicate(symbols)
```

### 1.2 Test Name Conversion

**Rules:**
- `test_type_inference` → `["type_inference", "TypeInference"]`
- `apply_subst_generic` → `["apply_subst", "ApplySubst"]`
- `parse_function_def` → `["parse_function_def", "ParseFunctionDef"]`

**Smart matching:**
1. Check imported modules first
2. Search in same file
3. Full repo search (via tags/LSP)
4. Fuzzy matching for close matches

### 1.3 Smart Path Resolution

**Logic:**
```python
def resolve_symbol_path(symbol, context):
    # If imported in spec file
    if symbol in context.imports:
        return symbol  # Short name
    
    # If defined locally
    if symbol in context.local_definitions:
        return symbol  # Short name
    
    # Otherwise use full path
    return context.lookup_full_path(symbol)
```

### 1.4 Enhanced Markdown Generation

**New sections:**
- Symbol index table
- Test-to-symbol links
- Related tests
- Source code links
- Quick TOC

---

## Phase 2: Root TOC Generation

### 2.1 Category Detection

**Automatic categorization from spec files:**

```python
CATEGORIES = {
    "Core Language": ["syntax", "types", "functions", "traits", "memory"],
    "Type System": ["type_inference", "types"],
    "Async/Concurrency": ["async_default", "suspension_operator", "concurrency"],
    "Advanced Features": ["capability_effects", "metaprogramming", "macro"],
    "Data Structures": ["data_structures"],
    "Testing": ["sandboxing"],
    "Modules": ["modules"]
}

def categorize_spec(spec_name):
    for category, specs in CATEGORIES.items():
        if any(s in spec_name for s in specs):
            return category
    return "Miscellaneous"
```

### 2.2 Root TOC Structure

**Generated:** `doc/spec/generated/README.md`

```markdown
# Simple Language Specifications - Index

**Generated:** 2026-01-09 05:53:54
**Total Specs:** 15
**Total Tests:** 294

## Quick Navigation

- [Core Language](#core-language) (5 specs)
- [Type System](#type-system) (2 specs)
- [Async/Concurrency](#asyncconcurrency) (3 specs)
- [Advanced Features](#advanced-features) (3 specs)
- [Data Structures](#data-structures) (1 spec)
- [Testing](#testing) (1 spec)

---

## Core Language

### [Syntax](syntax.md)
**Status:** Stable | **Tests:** 21 | **Feature IDs:** #10-19

Core syntax, execution modes, operators, and lexical structure.

**Key Symbols:** Token, Operator, ExecutionMode

### [Types](types.md)
**Status:** Stable | **Tests:** 17 | **Feature IDs:** #20-29

Type system, primitives, mutability, and generics.

**Key Symbols:** Type, TypeVar, Mutability

[... more specs ...]

---

## Type System

### [Type Inference](type_inference.md)
**Status:** Partial | **Tests:** 24 | **Feature IDs:** #13

Hindley-Milner type inference and unification.

**Key Symbols:** Context, Substitution, Unify

[... more specs ...]

---

## Cross-References

### By Symbol

| Symbol | Specs |
|--------|-------|
| Type | [types.md](types.md), [type_inference.md](type_inference.md) |
| Context | [type_inference.md](type_inference.md) |
| [... more ...] |

### By Feature ID

| Feature ID | Spec |
|------------|------|
| #10-19 | [syntax.md](syntax.md) |
| #20-29 | [types.md](types.md) |
| [... more ...] |

---

## Statistics

**By Status:**
- Stable: 7 specs
- Partial: 3 specs
- Draft: 5 specs

**By Test Count:**
- 30+ tests: 4 specs
- 20-29 tests: 6 specs
- 10-19 tests: 3 specs
- <10 tests: 2 specs

**Total Test Coverage:** 294 test cases
```

### 2.3 Per-Category TOC

**Generated:** `doc/spec/generated/categories/core_language.md`

```markdown
# Core Language Specifications

**Specs in Category:** 5

## Specifications

### 1. [Syntax](../syntax.md)
- **Status:** Stable
- **Tests:** 21 test cases
- **Feature IDs:** #10-19
- **Last Updated:** 2025-12-28

#### Test Cases
- Execution modes (2 tests)
- Operators (5 tests)
- Indentation (3 tests)
- [... more ...]

### 2. [Types](../types.md)
[... similar structure ...]

---

## Cross-References

Tests using multiple specs in this category:
- Generic types: [types.md](../types.md) + [type_inference.md](../type_inference.md)
```

---

## Implementation Steps

### Step 1: Update spec_gen.py

```python
# Add to spec_gen.py

def extract_symbols_from_test(test_case, imports):
    """Extract all symbol references using hybrid approach."""
    symbols = []
    
    # 1. Explicit docstring links
    symbols.extend(parse_docstring_links(test_case.docstring))
    
    # 2. Test name conversion
    symbols.extend(convert_test_name(test_case.name))
    
    # 3. Code scanning
    symbols.extend(scan_code_symbols(test_case.code, imports))
    
    return symbols

def generate_symbol_table(spec):
    """Generate symbol index table."""
    symbol_map = {}
    for test in spec.test_cases:
        for symbol in test.symbols:
            if symbol not in symbol_map:
                symbol_map[symbol] = []
            symbol_map[symbol].append(test.name)
    
    return symbol_map

def generate_quick_toc(spec):
    """Generate quick navigation TOC."""
    toc = ["## Quick Navigation\n"]
    toc.append("- [Overview](#overview)")
    toc.append("- [Symbols Reference](#symbols-reference)")
    toc.append(f"- [Test Cases](#test-cases) ({len(spec.test_cases)} tests)")
    toc.append("- [Source Code](#source-code)")
    return "\n".join(toc)
```

### Step 2: Create root TOC generator

```python
# New file: scripts/generate_spec_index.py

def generate_root_toc(specs_dir, output_dir):
    """Generate root TOC with categories."""
    specs = []
    for spec_file in specs_dir.glob("*_spec.spl"):
        spec = parse_spec_file(spec_file)
        spec.category = categorize_spec(spec_file.stem)
        specs.append(spec)
    
    # Group by category
    by_category = {}
    for spec in specs:
        if spec.category not in by_category:
            by_category[spec.category] = []
        by_category[spec.category].append(spec)
    
    # Generate main index
    generate_main_index(by_category, output_dir)
    
    # Generate per-category pages
    for category, cat_specs in by_category.items():
        generate_category_page(category, cat_specs, output_dir)
```

### Step 3: Update existing specs with symbol metadata

Add to spec header:
```simple
"""
# Type System Specification

**Status:** Stable
**Feature IDs:** #20-29
**Symbols:** Type, TypeVar, Mutability
**Module:** simple_type
"""
```

### Step 4: Test cases with hybrid linking

```simple
test "type_inference_basic":
    """
    Test basic type inference for literals.
    
    **Links:** Type::infer, Context::resolve
    **Related:** type_inference_complex
    """
    # Test name also implies: type_inference()
    let ctx = Context::new()
    let t = ctx.infer(42)  # Auto-detected: Context::infer
    assert t == Type::Int  # Auto-detected: Type::Int
```

---

## File Structure After Implementation

```
doc/spec/generated/
├── README.md                  # Root TOC with all categories
├── categories/
│   ├── core_language.md      # Core language specs TOC
│   ├── type_system.md        # Type system specs TOC
│   ├── async_concurrency.md  # Async specs TOC
│   └── ...
├── syntax.md                  # Enhanced with symbol links
├── types.md                   # Enhanced with symbol links
└── [13 more spec docs]        # All enhanced

tests/specs/
├── syntax_spec.spl            # Source specs (unchanged)
├── types_spec.spl
└── [13 more specs]
```

---

## Timeline

**Day 1: Core Features**
- ✅ Planning complete
- [ ] Update spec_gen.py with symbol extraction
- [ ] Implement test name conversion
- [ ] Add smart path resolution
- [ ] Generate enhanced markdown

**Day 2: TOC Generation**
- [ ] Create generate_spec_index.py
- [ ] Implement category detection
- [ ] Generate root README
- [ ] Generate category pages

**Day 3: Testing & Polish**
- [ ] Test with all 15 specs
- [ ] Verify all links work
- [ ] Add cross-references
- [ ] Update documentation

---

## Success Criteria

1. ✅ All specs have symbol tables
2. ✅ Test names auto-convert to symbols
3. ✅ Smart path resolution working
4. ✅ Root TOC with categories generated
5. ✅ Per-category TOC pages created
6. ✅ Cross-references working
7. ✅ All links valid

---

## Next Steps

1. Implement symbol extraction in spec_gen.py
2. Add test name conversion logic
3. Implement smart path resolution
4. Create root TOC generator
5. Test on all 15 specs
6. Commit and document

Let's start implementation!
